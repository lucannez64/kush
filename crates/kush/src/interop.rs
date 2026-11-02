//! Native interop support: the stable C bridge ABI, a linker-input descriptor,
//! and a Rust adapter source generator.
//!
//! # Trust boundary
//!
//! Kush checks the *Kush side* of every foreign declaration: the signature is
//! restricted to a small explicit C ABI, a `foreign` function cannot be
//! generic or used as a value, every call needs the `io` effect, and an opaque
//! `#[foreign("release")]` resource is released exactly once by ownership.
//! The foreign library itself is trusted code. Kush does not prove that it is
//! memory safe, does not validate pointer provenance, and does not protect
//! against a foreign function that violates the documented ABI.
//!
//! # Bridge ABI v1
//!
//! | Kush type | C type |
//! | --- | --- |
//! | `i8`/`u8`/`i16`/... | the matching `int8_t`/`uint8_t`/... |
//! | `f64`/`f32` | `double`/`float` |
//! | `Bool` | `int32_t` (0 or 1) |
//! | `&str`, `&Bytes`, `&String` | `const uint8_t *, int64_t` |
//! Inline slices are rejected: checked elements use word-sized storage.
//! | foreign resource | `void *` (`int64_t` on the wire) |
//!
//! A direct scalar/resource result is returned as the matching C value. For a
//! declared `Result<T, i64>` the function returns `int64_t` status (0 success,
//! non-zero = `Err(status)`) and writes `T` through a trailing `int64_t *out`
//! slot. Output words use Kush's checked scalar representation: integers are
//! sign/zero-extended, floats are raw IEEE-754 bits, and a resource is its
//! pointer as an integer.
//!
//! `AdapterSpec` generates ordinary Rust `extern "C"` shims around safe Rust
//! functions. Every shim catches unwinding at the boundary, so adapters must be
//! built with `panic = "unwind"`; a generated compile-time check rejects
//! `panic = "abort"` builds. Fallible shims map a Rust `Err(String)` to status 1
//! plus a retrievable message and a caught panic to status 2. Infallible shims
//! abort after recording a panic rather than crossing the boundary with a
//! half-written result.
//!
//! Error helpers use a configurable support-symbol prefix
//! ([`AdapterOptions::support_symbol_prefix`]) so multiple adapters can link
//! into one executable. The default prefix is `kush_bridge`; `kush bindgen`
//! derives a distinct prefix from the module path.
use std::fmt::Write as _;

/// One C ABI scalar type admitted by the bridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scalar {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
}
impl Scalar {
    fn rust(self) -> &'static str {
        match self {
            Scalar::I8 => "i8",
            Scalar::I16 => "i16",
            Scalar::I32 => "i32",
            Scalar::I64 => "i64",
            Scalar::U8 => "u8",
            Scalar::U16 => "u16",
            Scalar::U32 => "u32",
            Scalar::U64 => "u64",
            Scalar::F32 => "f32",
            Scalar::F64 => "f64",
            Scalar::Bool => "bool",
        }
    }
    fn abi_rust(self) -> &'static str {
        if self == Scalar::Bool {
            "i32"
        } else {
            self.rust()
        }
    }
    /// Direct (non-fallible) C return value. It uses the exact declared C type;
    /// the Kush backend extends it back to a checked word.
    fn direct(self, expression: &str) -> String {
        match self {
            Scalar::Bool => format!("if {expression} {{ 1i32 }} else {{ 0i32 }}"),
            Scalar::F32 | Scalar::F64 => expression.to_owned(),
            _ => format!("{expression} as {}", self.rust()),
        }
    }
    /// Canonical one-word encoding written to a fallible out slot.
    fn word(self, expression: &str) -> String {
        match self {
            Scalar::Bool => format!("if {expression} {{ 1i64 }} else {{ 0i64 }}"),
            Scalar::F64 => format!("{expression}.to_bits() as i64"),
            Scalar::F32 => format!("{expression}.to_bits() as i64"),
            Scalar::U64 => format!("{expression} as i64"),
            _ => format!("{expression} as i64"),
        }
    }
}

/// One generated shim parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Parameter {
    Scalar {
        name: String,
        ty: Scalar,
    },
    /// Borrowed UTF-8 text, validated at the boundary.
    Str {
        name: String,
    },
    /// Borrowed byte buffer.
    Bytes {
        name: String,
    },
    /// Borrowed opaque resource handle; the Rust function receives `&T`.
    Resource {
        name: String,
        resource: String,
    },
}

/// One generated shim result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResultType {
    Unit,
    Scalar(Scalar),
    /// An owned byte buffer. The Rust function returns `Vec<u8>`; the shim
    /// copies it into a Kush-owned `Bytes` allocation and returns that handle.
    Bytes,
    /// An owned resource; the shim boxes the Rust value and returns its handle.
    Resource(String),
}

/// One generated adapter function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// Kush-side display name, used only in generated comments.
    pub name: String,
    /// Exact exported C symbol. It must equal the symbol in the Kush
    /// `foreign "symbol" fn ...;` declaration.
    pub symbol: String,
    /// Safe Rust function path, for example `Bridge::sha256` or
    /// `bridge::parse`.
    pub rust_path: String,
    pub parameters: Vec<Parameter>,
    pub result: ResultType,
    /// When true the Rust function returns `Result<T, String>` and the C shim
    /// returns a status with an out slot. When false the Rust function returns
    /// `T` directly.
    pub fallible: bool,
}

/// One opaque owned Rust resource exposed to Kush.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Resource {
    /// Kush type name, matching `#[foreign("release")] struct Name {}`.
    pub name: String,
    /// Rust type stored behind the handle, for example `Client`.
    pub rust_type: String,
    /// Exact exported release symbol, matching `#[foreign("release_symbol")]`.
    pub release_symbol: String,
}

/// Options for generated adapter source.
///
/// The support prefix names the two `#[no_mangle]` error-retrieval symbols
/// emitted by every generated file. A caller that links more than one adapter
/// must give each one a distinct prefix; `kush bindgen` derives it from the
/// declared Kush module path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdapterOptions {
    /// Identifier prefix, for example `kush_example_bridge`.
    pub support_symbol_prefix: String,
}
impl Default for AdapterOptions {
    fn default() -> Self {
        Self {
            support_symbol_prefix: "kush_bridge".to_owned(),
        }
    }
}
impl AdapterOptions {
    pub fn new(support_symbol_prefix: impl Into<String>) -> Self {
        Self {
            support_symbol_prefix: support_symbol_prefix.into(),
        }
    }
}

/// A complete generated adapter source file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AdapterSpec {
    pub resources: Vec<Resource>,
    pub functions: Vec<Function>,
}
impl AdapterSpec {
    /// Validate every symbol and Rust path before generating source. The
    /// generator is developer-facing, but rejecting malformed names keeps
    /// generated code readable and avoids accidental source injection.
    pub fn validate(&self) -> std::result::Result<(), String> {
        let mut symbols = std::collections::BTreeSet::new();
        let mut resource_names = std::collections::BTreeSet::new();
        for resource in &self.resources {
            validate_identifier(&resource.name, "resource name")?;
            validate_symbol(&resource.release_symbol)?;
            validate_rust_path(&resource.rust_type, "resource Rust type")?;
            if !resource_names.insert(resource.name.clone()) {
                return Err(format!("duplicate resource name '{}'", resource.name));
            }
            if !symbols.insert(resource.release_symbol.clone()) {
                return Err(format!(
                    "duplicate generated symbol '{}'",
                    resource.release_symbol
                ));
            }
        }
        for function in &self.functions {
            validate_identifier(&function.name, "Kush function name")?;
            validate_symbol(&function.symbol)?;
            validate_rust_path(&function.rust_path, "Rust function path")?;
            if !symbols.insert(function.symbol.clone()) {
                return Err(format!("duplicate generated symbol '{}'", function.symbol));
            }
            // Match the identifiers that actually appear in the generated C
            // signature. `kush_out` is added for fallible non-Unit results, and
            // borrowed buffers expand to `<name>_data` and `<name>_len`.
            let mut c_names = std::collections::BTreeSet::new();
            for parameter in &function.parameters {
                let name = match parameter {
                    Parameter::Scalar { name, .. }
                    | Parameter::Str { name }
                    | Parameter::Bytes { name }
                    | Parameter::Resource { name, .. } => name,
                };
                validate_identifier(name, "parameter name")?;
                reject_support_name(name)?;
                if name == "kush_out" {
                    return Err(format!(
                        "parameter name 'kush_out' in '{}' is reserved for the generated result slot",
                        function.symbol
                    ));
                }
                insert_c_parameter(&mut c_names, name, &function.symbol)?;
                if matches!(parameter, Parameter::Str { .. } | Parameter::Bytes { .. }) {
                    insert_c_parameter(&mut c_names, &format!("{name}_data"), &function.symbol)?;
                    insert_c_parameter(&mut c_names, &format!("{name}_len"), &function.symbol)?;
                }
                if let Parameter::Resource { resource, .. } = parameter
                    && !self
                        .resources
                        .iter()
                        .any(|declared| &declared.name == resource)
                {
                    return Err(format!(
                        "parameter '{}' names undeclared resource '{}'",
                        function.symbol, resource
                    ));
                }
            }
            if function.fallible && !matches!(function.result, ResultType::Unit) {
                insert_c_parameter(&mut c_names, "kush_out", &function.symbol)?;
            }
            if let ResultType::Resource(resource) = &function.result
                && !self
                    .resources
                    .iter()
                    .any(|declared| &declared.name == resource)
            {
                return Err(format!(
                    "function '{}' returns undeclared resource '{}'",
                    function.symbol, resource
                ));
            }
        }
        Ok(())
    }
    /// Generate a self-contained Rust source file using the default
    /// `kush_bridge` support prefix.
    pub fn generate(&self) -> std::result::Result<String, String> {
        self.generate_with_options(&AdapterOptions::default())
    }

    /// Generate a self-contained Rust source file suitable for
    /// `include!`/`mod` in an ordinary library crate. The file contains the
    /// bridge support module, resource release shims, error retrieval, and one
    /// `#[unsafe(no_mangle)] extern "C"` shim per function.
    ///
    /// Besides `<prefix>_last_error(out, capacity)`, the generated support
    /// module exposes `<prefix>_last_error_bytes(out: *mut i64) -> i64`, which
    /// returns status 0 and writes a Kush-owned `Bytes` handle containing the
    /// latest error text, status 1 when there is no error, 2 for a null out
    /// pointer, and 3 when the runtime cannot allocate the buffer. That shape is
    /// directly callable from a checked Kush `Result<Bytes, i64>` declaration;
    /// [`crate::bindgen`] emits the matching declaration.
    pub fn generate_with_options(
        &self,
        options: &AdapterOptions,
    ) -> std::result::Result<String, String> {
        self.validate()?;
        validate_identifier(&options.support_symbol_prefix, "support symbol prefix")?;
        let error_symbol = format!("{}_last_error", options.support_symbol_prefix);
        let error_bytes_symbol = format!("{}_last_error_bytes", options.support_symbol_prefix);
        let mut out = String::new();
        out.push_str(
            "// @generated by kush::interop::AdapterSpec. Do not edit by hand.\n\
             // Trusted boundary: the C ABI is checked on the Kush side; the Rust\n\
             // implementations below remain trusted code.\n\
             // This file is an item sequence and works both as a module file and\n\
             // through `include!` inside a module. It requires panic=unwind so the\n\
             // generated `catch_unwind` boundary can turn a panic into status 2.\n\
             #[cfg(panic = \"abort\")]\n\
             compile_error!(\"kush generated adapters require panic=unwind so panics can be contained at the C boundary\");\n\n\
             #[allow(dead_code, clippy::missing_safety_doc)]\n             mod kush_bridge_support {\n\
             \x20   use std::cell::RefCell;\n\
             \x20   thread_local! {\n\
             \x20       static LAST_ERROR: RefCell<Option<String>> = const { RefCell::new(None) };\n\
             \x20   }\n\
             \x20   pub fn set_error(message: String) {\n\
             \x20       LAST_ERROR.with(|slot| *slot.borrow_mut() = Some(message));\n\
             \x20   }\n\
             \x20   pub fn clear_error() {\n\
             \x20       LAST_ERROR.with(|slot| *slot.borrow_mut() = None);\n\
             \x20   }\n\
             \x20   pub fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {\n\
             \x20       if let Some(message) = payload.downcast_ref::<&str>() {\n\
             \x20           (*message).to_owned()\n\
             \x20       } else if let Some(message) = payload.downcast_ref::<String>() {\n\
             \x20           message.clone()\n\
             \x20       } else {\n\
             \x20           \"foreign Rust adapter panicked\".to_owned()\n\
             \x20       }\n\
             \x20   }\n\
             \x20   /// Copy the most recent adapter error into a caller buffer.\n\
             \x20   /// Returns the full message length, or -1 when there is no error.\n\
             \x20   #[unsafe(no_mangle)]\n\
             \x20   pub extern \"C\" fn __KUSH_LAST_ERROR__(out: *mut u8, capacity: i64) -> i64 {\n\
             \x20       LAST_ERROR.with(|slot| {\n\
             \x20           let borrow = slot.borrow();\n\
             \x20           let Some(message) = borrow.as_deref() else { return -1 };\n\
             \x20           let bytes = message.as_bytes();\n\
             \x20           let length = bytes.len() as i64;\n\
             \x20           if !out.is_null() && capacity > 0 {\n\
             \x20               let count = bytes.len().min(capacity as usize);\n\
             \x20               unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), out, count) }\n\
             \x20           }\n\
             \x20           length\n\
             \x20       })\n\
             \x20   }\n\
             \x20   /// Copy the most recent adapter error into a Kush-owned `Bytes`\n\
             \x20   /// allocation. Status 0 writes the handle, 1 means no error, 2 is a\n\
             \x20   /// null out pointer, and 3 means the runtime allocation failed.\n\
             \x20   #[unsafe(no_mangle)]\n\
             \x20   pub extern \"C\" fn __KUSH_LAST_ERROR_BYTES__(out: *mut i64) -> i64 {\n\
             \x20       LAST_ERROR.with(|slot| {\n\
             \x20           let borrow = slot.borrow();\n\
             \x20           let Some(message) = borrow.as_deref() else { return 1 };\n\
             \x20           if out.is_null() { return 2 }\n\
             \x20           let bytes = message.as_bytes();\n\
             \x20           let handle = unsafe { super::kush_bytes_from(bytes.as_ptr(), bytes.len() as i64) };\n\
             \x20           if handle == 0 { return 3 }\n\
             \x20           unsafe { *out = handle };\n\
             \x20           0\n\
             \x20       })\n\
             \x20   }\n\
             \x20   pub fn guard(\n\
             \x20       name: &str,\n\
             \x20       body: impl FnOnce() -> Result<(), String> + std::panic::UnwindSafe,\n\
             \x20   ) -> i64 {\n\
             \x20       clear_error();\n\
             \x20       match std::panic::catch_unwind(std::panic::AssertUnwindSafe(body)) {\n\
             \x20           Ok(Ok(())) => 0,\n\
             \x20           Ok(Err(message)) => { set_error(message); 1 }\n\
             \x20           Err(payload) => {\n\
             \x20               let message = panic_message(payload);\n\
             \x20               set_error(format!(\"{name} panicked: {message}\"));\n\
             \x20               2\n\
             \x20           }\n\
             \x20       }\n\
             \x20   }\n\
             \x20   pub fn abort_on_panic<T>(name: &str, body: impl FnOnce() -> T) -> T {\n\
             \x20       match std::panic::catch_unwind(std::panic::AssertUnwindSafe(body)) {\n\
             \x20           Ok(value) => value,\n\
             \x20           Err(payload) => {\n\
             \x20               let message = panic_message(payload);\n\
             \x20               set_error(format!(\"{name} panicked: {message}\"));\n\
             \x20               eprintln!(\"{name} panicked: {message}\");\n\
             \x20               std::process::abort()\n\
             \x20           }\n\
             \x20       }\n\
             \x20   }\n\
             \x20   pub unsafe fn input_bytes<'a>(data: *const u8, length: i64) -> Result<&'a [u8], String> {\n\
             \x20       if length < 0 { return Err(\"negative byte length\".into()) }\n\
             \x20       if length == 0 { return Ok(&[]) }\n\
             \x20       if data.is_null() { return Err(\"null byte pointer with non-zero length\".into()) }\n\
             \x20       Ok(unsafe { std::slice::from_raw_parts(data, length as usize) })\n\
             \x20   }\n\
             \x20   pub unsafe fn input_bytes_mut<'a>(data: *mut u8, length: i64) -> Result<&'a mut [u8], String> {\n\
             \x20       if length < 0 { return Err(\"negative byte length\".into()) }\n\
             \x20       if length == 0 { return Ok(&mut []) }\n\
             \x20       if data.is_null() { return Err(\"null byte pointer with non-zero length\".into()) }\n\
             \x20       Ok(unsafe { std::slice::from_raw_parts_mut(data, length as usize) })\n\
             \x20   }\n\
             \x20   pub unsafe fn input_str<'a>(data: *const u8, length: i64) -> Result<&'a str, String> {\n\
             \x20       let bytes = unsafe { input_bytes(data, length) }?;\n\
             \x20       std::str::from_utf8(bytes).map_err(|error| format!(\"invalid UTF-8 at the Kush boundary: {error}\"))\n\
             \x20   }\n\
             \x20   pub fn write_word(out: *mut i64, word: i64) -> Result<(), String> {\n\
             \x20       if out.is_null() { return Err(\"null out-pointer\".into()) }\n\
             \x20       unsafe { *out = word };\n\
             \x20       Ok(())\n\
             \x20   }\n\
             }\n\
             use kush_bridge_support::*;\n\n\
             unsafe extern \"C\" {\n\
             \x20   /// Supplied by the Kush runtime linked into the final binary.\n\
             \x20   fn kush_bytes_from(source: *const u8, length: i64) -> i64;\n\
             }\n\n",
        );
        out = out
            .replace("__KUSH_LAST_ERROR_BYTES__", &error_bytes_symbol)
            .replace("__KUSH_LAST_ERROR__", &error_symbol);
        for resource in &self.resources {
            let release = &resource.release_symbol;
            let ty = &resource.rust_type;
            let _ = writeln!(
                out,
                "/// Release the host-owned `{ty}` exactly once. Kush drop glue calls\n\
                 /// this only after ownership proves the handle is consumed.\n\
                 #[unsafe(no_mangle)]\n\
                 pub extern \"C\" fn {release}(handle: i64) {{\n\
                 \x20   if handle == 0 {{ return }}\n\
                 \x20   let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{\n\
                 \x20       drop(unsafe {{ Box::from_raw(handle as *mut {ty}) }});\n\
                 \x20   }}));\n\
                 }}\n"
            );
        }
        for function in &self.functions {
            out.push_str(&generate_function(self, function));
        }
        Ok(out)
    }
}

fn generate_function(spec: &AdapterSpec, function: &Function) -> String {
    let mut c_parameters = Vec::new();
    let mut rust_arguments = Vec::new();
    let mut setup = String::new();
    let mut setup_abort = String::new();
    let abort = |_name: &str| {
        "        .unwrap_or_else(|message: String| { kush_bridge_support::set_error(message); std::process::abort() })\n"
            .to_owned()
    };
    for (index, parameter) in function.parameters.iter().enumerate() {
        match parameter {
            Parameter::Scalar { name, ty } => {
                c_parameters.push(format!(
                    "{name}: {}",
                    if *ty == Scalar::Bool {
                        "i32"
                    } else {
                        ty.rust()
                    }
                ));
                if *ty == Scalar::Bool {
                    rust_arguments.push(format!("{name} != 0"));
                } else {
                    rust_arguments.push(name.clone());
                }
            }
            Parameter::Str { name } => {
                let pointer = format!("{name}_data");
                let length = format!("{name}_len");
                c_parameters.push(format!("{pointer}: *const u8"));
                c_parameters.push(format!("{length}: i64"));
                setup.push_str(&format!(
                    "        let {name} = unsafe {{ input_str({pointer}, {length}) }}?;\n"
                ));
                setup_abort.push_str(&format!(
                    "        let {name} = unsafe {{ input_str({pointer}, {length}) }}{}",
                    abort(name)
                ));
                rust_arguments.push(name.clone());
            }
            Parameter::Bytes { name } => {
                let pointer = format!("{name}_data");
                let length = format!("{name}_len");
                c_parameters.push(format!("{pointer}: *const u8"));
                c_parameters.push(format!("{length}: i64"));
                setup.push_str(&format!(
                    "        let {name} = unsafe {{ input_bytes({pointer}, {length}) }}?;\n"
                ));
                setup_abort.push_str(&format!(
                    "        let {name} = unsafe {{ input_bytes({pointer}, {length}) }}{}",
                    abort(name)
                ));
                rust_arguments.push(name.clone());
            }
            Parameter::Resource { name, resource } => {
                let rust_type = &spec
                    .resources
                    .iter()
                    .find(|declared| &declared.name == resource)
                    .expect("validated resource")
                    .rust_type;
                c_parameters.push(format!("{name}: i64"));
                setup.push_str(&format!(
                    "        if {name} == 0 {{ return Err(\"null {resource} handle\".into()) }}\n\
                     \x20       let {name} = unsafe {{ &*({name} as *const {rust_type}) }};\n"
                ));
                setup_abort.push_str(&format!(
                    "        if {name} == 0 {{ kush_bridge_support::set_error(\"null {resource} handle\".into()); std::process::abort() }}\n\
                     \x20       let {name} = unsafe {{ &*({name} as *const {rust_type}) }};\n"
                ));
                rust_arguments.push(name.clone());
            }
        }
        let _ = index;
    }
    let call = format!("{}({})", function.rust_path, rust_arguments.join(", "));
    let mut out = String::new();
    let _ = writeln!(
        out,
        "/// Kush `{}` -> `{}`\n#[unsafe(no_mangle)]",
        function.name, function.symbol
    );
    if function.fallible {
        let out_parameter = if !matches!(function.result, ResultType::Unit) {
            c_parameters.push("kush_out: *mut i64".to_owned());
            true
        } else {
            false
        };
        let _ = writeln!(
            out,
            "pub extern \"C\" fn {}({}) -> i64 {{",
            function.symbol,
            c_parameters.join(", ")
        );
        let _ = writeln!(
            out,
            "    guard(\"{}\", || {{\n{}        match {call} {{\n            Ok({}) => {{",
            function.symbol,
            setup,
            if matches!(function.result, ResultType::Unit) {
                "()"
            } else {
                "value"
            }
        );
        match &function.result {
            ResultType::Unit => out.push_str("                Ok(())\n"),
            ResultType::Scalar(scalar) => {
                let _ = writeln!(
                    out,
                    "                write_word(kush_out, {})?;\n                Ok(())",
                    scalar.word("value")
                );
            }
            ResultType::Bytes => out.push_str(
                "                write_word(\n                    kush_out,\n                    unsafe { kush_bytes_from(value.as_ptr(), value.len() as i64) },\n                )?;\n                Ok(())\n",
            ),
            ResultType::Resource(resource) => {
                let ty = &spec
                    .resources
                    .iter()
                    .find(|declared| &declared.name == resource)
                    .expect("validated resource")
                    .rust_type;
                // The box is created only after the null check so a null out
                // slot cannot orphan a freshly allocated handle.
                let _ = writeln!(
                    out,
                    "                if kush_out.is_null() {{ return Err(\"null out-pointer\".into()) }}\n                write_word(kush_out, Box::into_raw(Box::new(value)) as i64)?;\n                Ok(())"
                );
                let _ = ty;
            }
        }
        out.push_str(
            "            }\n            Err(message) => Err(message),\n        }\n    })\n}\n\n",
        );
        let _ = out_parameter;
    } else {
        let _ = writeln!(
            out,
            "pub extern \"C\" fn {}({}) -> {} {{",
            function.symbol,
            c_parameters.join(", "),
            match &function.result {
                ResultType::Scalar(scalar) => scalar.abi_rust(),
                _ => "i64",
            }
        );
        match &function.result {
            ResultType::Unit => {
                let _ = writeln!(
                    out,
                    "    abort_on_panic(\"{}\", || {{\n{}        let _ = {call};\n    }});\n    0\n}}\n",
                    function.symbol, setup_abort
                );
            }
            ResultType::Scalar(scalar) => {
                let _ = writeln!(
                    out,
                    "    let value = abort_on_panic(\"{}\", || {{\n{}        {call}\n    }});\n    {}\n}}\n",
                    function.symbol,
                    setup_abort,
                    scalar.direct("value")
                );
            }
            ResultType::Bytes => {
                let _ = writeln!(
                    out,
                    "    let value = abort_on_panic(\"{}\", || {{\n{}        {call}\n    }});\n    unsafe {{ kush_bytes_from(value.as_ptr(), value.len() as i64) }}\n}}\n",
                    function.symbol, setup_abort
                );
            }
            ResultType::Resource(resource) => {
                let ty = &spec
                    .resources
                    .iter()
                    .find(|declared| &declared.name == resource)
                    .expect("validated resource")
                    .rust_type;
                let _ = ty;
                let _ = writeln!(
                    out,
                    "    let value = abort_on_panic(\"{}\", || {{\n{}        {call}\n    }});\n    Box::into_raw(Box::new(value)) as i64\n}}\n",
                    function.symbol, setup_abort
                );
            }
        }
    }
    out
}

fn insert_c_parameter(
    names: &mut std::collections::BTreeSet<String>,
    name: &str,
    symbol: &str,
) -> std::result::Result<(), String> {
    if !names.insert(name.to_owned()) {
        return Err(format!(
            "generated C parameter name '{name}' collides in '{symbol}'"
        ));
    }
    Ok(())
}

fn validate_identifier(name: &str, what: &str) -> std::result::Result<(), String> {
    let mut characters = name.chars();
    let valid = characters
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && characters.all(|character| character == '_' || character.is_ascii_alphanumeric());
    if !valid {
        return Err(format!(
            "{what} '{name}' must be a Rust/C identifier ([A-Za-z_][A-Za-z0-9_]*)"
        ));
    }
    if name == "_" {
        return Err(format!("{what} '_' is a wildcard, not a name"));
    }
    if is_rust_keyword(name) {
        return Err(format!(
            "{what} '{name}' is a Rust keyword; use safe glue with a non-keyword name"
        ));
    }
    Ok(())
}

fn is_rust_keyword(name: &str) -> bool {
    matches!(
        name,
        "as" | "async"
            | "await"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "gen"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "try"
            | "typeof"
            | "union"
            | "unsized"
            | "virtual"
            | "yield"
    )
}

fn reject_support_name(name: &str) -> std::result::Result<(), String> {
    if [
        "guard",
        "abort_on_panic",
        "write_word",
        "input_bytes",
        "input_str",
        "kush_bytes_from",
        "kush_bridge_support",
        "set_error",
        "clear_error",
    ]
    .contains(&name)
    {
        return Err(format!(
            "name '{name}' is reserved by the generated bridge support"
        ));
    }
    Ok(())
}

fn validate_symbol(symbol: &str) -> std::result::Result<(), String> {
    validate_identifier(symbol, "C symbol")?;
    reject_support_name(symbol)
}
fn validate_rust_path(path: &str, what: &str) -> std::result::Result<(), String> {
    if path.is_empty() {
        return Err(format!("{what} must not be empty"));
    }
    for (index, segment) in path.split("::").enumerate() {
        if index == 0 && matches!(segment, "crate" | "self" | "super" | "Self") {
            continue;
        }
        validate_identifier(segment, what)?;
    }
    Ok(())
}
