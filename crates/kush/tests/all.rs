//! Every integration test of the crate, as modules of one test binary.
//!
//! One binary links the compiler once instead of once per test file;
//! nextest still runs each test in its own process. A new test file in
//! `tests/` needs a line here.

#[path = "abortive_handlers.rs"]
mod abortive_handlers;
#[path = "advanced_types_effects.rs"]
mod advanced_types_effects;
#[path = "allocator_containers.rs"]
mod allocator_containers;
#[path = "allocator_pool.rs"]
mod allocator_pool;
#[path = "arithmetic_proofs.rs"]
mod arithmetic_proofs;
#[path = "async.rs"]
mod async_tasks;
#[path = "bindgen.rs"]
mod bindgen;
#[path = "borrowed_methods.rs"]
mod borrowed_methods;
#[path = "borrowed_record_mutation.rs"]
mod borrowed_record_mutation;
#[path = "borrowed_records.rs"]
mod borrowed_records;
#[path = "borrowed_task_exit.rs"]
mod borrowed_task_exit;
#[path = "borrowing_extensions.rs"]
mod borrowing_extensions;
#[path = "borrowing_references.rs"]
mod borrowing_references;
#[path = "borrowing_safety.rs"]
mod borrowing_safety;
#[path = "bytes.rs"]
mod bytes;
#[path = "callable_lifetimes.rs"]
mod callable_lifetimes;
#[path = "check.rs"]
mod check;
#[path = "cli.rs"]
mod cli;
#[path = "closure_captures.rs"]
mod closure_captures;
#[path = "copyable_result_transfer.rs"]
mod copyable_result_transfer;
#[path = "default_methods.rs"]
mod default_methods;
#[path = "deferred_overflow.rs"]
mod deferred_overflow;
#[path = "dependent.rs"]
mod dependent;
#[path = "disjunctive_proofs.rs"]
mod disjunctive_proofs;
#[path = "dyn_objects.rs"]
mod dyn_objects;
#[path = "dyn_receivers.rs"]
mod dyn_receivers;
#[path = "effect_capabilities.rs"]
mod effect_capabilities;
#[path = "effect_constraints.rs"]
mod effect_constraints;
#[path = "effect_row_inference.rs"]
mod effect_row_inference;
#[path = "effect_row_laws.rs"]
mod effect_row_laws;
#[path = "effect_state_machines.rs"]
mod effect_state_machines;
#[path = "enums.rs"]
mod enums;
#[path = "executable.rs"]
mod executable;
#[path = "ffi.rs"]
mod ffi;
#[path = "field_privacy.rs"]
mod field_privacy;
#[path = "floats.rs"]
mod floats;
#[path = "frontend.rs"]
mod frontend;
#[path = "functions.rs"]
mod functions;
#[path = "generic_traits.rs"]
mod generic_traits;
#[path = "gpu_subset.rs"]
mod gpu_subset;
#[path = "grade_algebras.rs"]
mod grade_algebras;
#[path = "grade_demand_hint.rs"]
mod grade_demand_hint;
#[path = "grade_inference.rs"]
mod grade_inference;
#[path = "grade_obligations.rs"]
mod grade_obligations;
#[path = "grade_zero_erasure.rs"]
mod grade_zero_erasure;
#[path = "grades.rs"]
mod grades;
#[path = "handler_bookkeeping.rs"]
mod handler_bookkeeping;
#[path = "headerless_buffers.rs"]
mod headerless_buffers;
#[path = "host_api.rs"]
mod host_api;
#[path = "implicit_capabilities.rs"]
mod implicit_capabilities;
#[path = "implied_bounds.rs"]
mod implied_bounds;
#[path = "import_alias.rs"]
mod import_alias;
#[path = "index_disjointness.rs"]
mod index_disjointness;
#[path = "induction.rs"]
mod induction;
#[path = "integer_refutation.rs"]
mod integer_refutation;
#[path = "integers.rs"]
mod integers;
#[path = "integrated_core.rs"]
mod integrated_core;
#[path = "interop.rs"]
mod interop;
#[path = "json.rs"]
mod json;
#[path = "kernel.rs"]
mod kernel;
#[path = "kernel_budget.rs"]
mod kernel_budget;
#[path = "kernel_diff.rs"]
mod kernel_diff;
#[path = "kernel_exchange.rs"]
mod kernel_exchange;
#[path = "kernel_in_kush.rs"]
mod kernel_in_kush;
#[path = "kernel_spec.rs"]
mod kernel_spec;
#[path = "kernel_spec_diff.rs"]
mod kernel_spec_diff;
#[path = "lambda_inference.rs"]
mod lambda_inference;
#[path = "language_limits.rs"]
mod language_limits;
#[path = "language_server.rs"]
mod language_server;
#[path = "length_refined_fields.rs"]
mod length_refined_fields;
#[path = "lifetime_integration_baseline.rs"]
mod lifetime_integration_baseline;
#[path = "lifetime_rowvars.rs"]
mod lifetime_rowvars;
#[path = "lifetime_struct_results.rs"]
mod lifetime_struct_results;
#[path = "lifetime_variance.rs"]
mod lifetime_variance;
#[path = "lifetimes.rs"]
mod lifetimes;
#[path = "linear_resources.rs"]
mod linear_resources;
#[path = "linear_tasks.rs"]
mod linear_tasks;
#[path = "llvm_backend.rs"]
mod llvm_backend;
#[path = "logical_data.rs"]
mod logical_data;
#[path = "logical_lambdas.rs"]
mod logical_lambdas;
#[path = "memory_completion.rs"]
mod memory_completion;
#[path = "methods.rs"]
mod methods;
#[path = "milestone.rs"]
mod milestone;
#[path = "mir.rs"]
mod mir;
#[path = "multishot_capabilities.rs"]
mod multishot_capabilities;
#[path = "mutable_text.rs"]
mod mutable_text;
#[path = "native.rs"]
mod native;
#[path = "native_release.rs"]
mod native_release;
#[path = "native_stdio.rs"]
mod native_stdio;
#[path = "natural.rs"]
mod natural;
#[path = "niche_layout.rs"]
mod niche_layout;
#[path = "overflow_elision.rs"]
mod overflow_elision;
#[path = "ownership.rs"]
mod ownership;
#[path = "panic_catch.rs"]
mod panic_catch;
#[path = "places_and_constants.rs"]
mod places_and_constants;
#[path = "postconditions.rs"]
mod postconditions;
#[path = "project.rs"]
mod project;
#[path = "proof_fuzz_engine.rs"]
mod proof_fuzz_engine;
#[path = "proof_fuzz_entries.rs"]
mod proof_fuzz_entries;
#[path = "proof_fuzz_harness.rs"]
mod proof_fuzz_harness;
#[path = "proof_fuzz_native.rs"]
mod proof_fuzz_native;
#[path = "proof_fuzz_records.rs"]
mod proof_fuzz_records;
#[path = "proof_fuzz_shrink.rs"]
mod proof_fuzz_shrink;
#[path = "proof_obligations.rs"]
mod proof_obligations;
#[path = "record_layout.rs"]
mod record_layout;
#[path = "recursive_lifetimes.rs"]
mod recursive_lifetimes;
#[path = "resolve.rs"]
mod resolve;
#[path = "result_grade_inference.rs"]
mod result_grade_inference;
#[path = "reuse.rs"]
mod reuse;
#[path = "review_regressions.rs"]
mod review_regressions;
#[path = "runtime_cache.rs"]
mod runtime_cache;
#[path = "runtime_indices.rs"]
mod runtime_indices;
#[path = "runtime_length_extensions.rs"]
mod runtime_length_extensions;
#[path = "rust_export.rs"]
mod rust_export;
#[path = "scalar_proofs.rs"]
mod scalar_proofs;
#[path = "shift_elision.rs"]
mod shift_elision;
#[path = "simd_cpu.rs"]
mod simd_cpu;
#[path = "simd_ops.rs"]
mod simd_ops;
#[path = "simd_types.rs"]
mod simd_types;
#[path = "simd_x86_sha.rs"]
mod simd_x86_sha;
#[path = "slices.rs"]
mod slices;
#[path = "slices_native.rs"]
mod slices_native;
#[path = "stack_exhaustion.rs"]
mod stack_exhaustion;
#[path = "staging.rs"]
mod staging;
#[path = "stateful_handlers.rs"]
mod stateful_handlers;
#[path = "std_bincode.rs"]
mod std_bincode;
#[path = "std_crc_bytemap.rs"]
mod std_crc_bytemap;
#[path = "std_crypto.rs"]
mod std_crypto;
#[path = "std_file.rs"]
mod std_file;
#[path = "std_helpers.rs"]
mod std_helpers;
#[path = "std_natural.rs"]
mod std_natural;
#[path = "std_net_udp.rs"]
mod std_net_udp;
#[path = "std_proc_net.rs"]
mod std_proc_net;
#[path = "std_sys.rs"]
mod std_sys;
#[path = "stdio.rs"]
mod stdio;
#[path = "strings.rs"]
mod strings;
#[path = "struct_update.rs"]
mod struct_update;
#[path = "subtyping.rs"]
mod subtyping;
#[path = "tactics.rs"]
mod tactics;
#[path = "task_borrows.rs"]
mod task_borrows;
#[path = "threads.rs"]
mod threads;
#[path = "todo_app.rs"]
mod todo_app;
#[path = "trait_advanced.rs"]
mod trait_advanced;
#[path = "traits.rs"]
mod traits;
#[path = "tuples.rs"]
mod tuples;
#[path = "universes.rs"]
mod universes;
#[path = "vec_push_loops.rs"]
mod vec_push_loops;
#[path = "vector_reuse.rs"]
mod vector_reuse;
#[path = "view_exclusivity.rs"]
mod view_exclusivity;
#[path = "web_core.rs"]
mod web_core;
#[path = "web_http1.rs"]
mod web_http1;
#[path = "web_net.rs"]
mod web_net;
#[path = "web_reactor.rs"]
mod web_reactor;
#[path = "web_server.rs"]
mod web_server;
#[path = "web_url.rs"]
mod web_url;
