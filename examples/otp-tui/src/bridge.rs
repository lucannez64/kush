//! Trusted library boundary. Secret-bearing state stays behind an opaque handle.
use crossterm::{
    cursor,
    event::{self, Event, KeyCode, KeyEventKind, KeyModifiers},
    execute,
    terminal::{self, EnterAlternateScreen, LeaveAlternateScreen},
};
use data_encoding::{BASE32, BASE32_NOPAD};
use hmac::{Hmac, Mac};
use sha1::Sha1;
use sha2::{Sha256, Sha512};
use std::{
    cell::RefCell,
    collections::BTreeMap,
    io::{self, IsTerminal, Write},
    time::{Duration, SystemTime, UNIX_EPOCH},
};
use unicode_width::UnicodeWidthChar;
use url::Url;
use zeroize::{Zeroize, Zeroizing};

type Fallible<T> = Result<T, String>;
const MAX_INPUT: usize = 8192;
const MAX_ENTRIES: usize = 1000;
#[derive(Clone, Copy)]
enum Algorithm {
    Sha1,
    Sha256,
    Sha512,
}
struct Entry {
    label: String,
    secret: Zeroizing<Vec<u8>>,
    algorithm: Algorithm,
    digits: u32,
    period: u64,
    counter: Option<u64>,
}
impl Entry {
    fn parse(input: &[u8]) -> Fallible<Self> {
        if input.is_empty() || input.len() > MAX_INPUT {
            return Err("URI must contain 1..8192 bytes".into());
        }
        let text = std::str::from_utf8(input).map_err(|_| "URI must be UTF-8")?;
        if text.chars().any(char::is_control) {
            return Err("URI must be a single line without control characters".into());
        }
        let url = Url::parse(text).map_err(|_| "Invalid otpauth URI")?;
        if url.scheme() != "otpauth"
            || !url.username().is_empty()
            || url.password().is_some()
            || url.port().is_some()
            || url.fragment().is_some()
        {
            return Err("Expected an otpauth://totp/ or otpauth://hotp/ URI".into());
        }
        let hotp = match url.host_str() {
            Some("totp") => false,
            Some("hotp") => true,
            _ => return Err("Unsupported OTP type".into()),
        };
        let mut query = BTreeMap::new();
        for (key, value) in url.query_pairs() {
            let key = key.into_owned();
            if !matches!(
                key.as_str(),
                "secret" | "issuer" | "algorithm" | "digits" | "period" | "counter"
            ) {
                return Err("Unsupported OTP parameter".into());
            }
            if query
                .insert(key, Zeroizing::new(value.into_owned()))
                .is_some()
            {
                return Err("Duplicate OTP parameter".into());
            }
        }
        let get = |name: &str| query.get(name).map(|s| s.as_str());
        let encoded = get("secret").ok_or("Missing secret")?;
        let upper = Zeroizing::new(encoded.to_ascii_uppercase());
        let secret = Zeroizing::new(
            if upper.contains('=') {
                BASE32.decode(upper.as_bytes())
            } else {
                BASE32_NOPAD.decode(upper.as_bytes())
            }
            .map_err(|_| "Invalid Base32 secret")?,
        );
        if secret.is_empty() {
            return Err("Empty secret".into());
        }
        let algorithm = match get("algorithm")
            .unwrap_or("SHA1")
            .to_ascii_uppercase()
            .as_str()
        {
            "SHA1" => Algorithm::Sha1,
            "SHA256" => Algorithm::Sha256,
            "SHA512" => Algorithm::Sha512,
            _ => return Err("Algorithm must be SHA1, SHA256, or SHA512".into()),
        };
        let digits = get("digits")
            .unwrap_or("6")
            .parse::<u32>()
            .map_err(|_| "Invalid digits")?;
        if !(6..=10).contains(&digits) {
            return Err("Digits must be between 6 and 10".into());
        }
        let period = get("period")
            .unwrap_or("30")
            .parse::<u64>()
            .map_err(|_| "Invalid period")?;
        if period == 0 || period > i64::MAX as u64 {
            return Err("Period must be a positive signed 64-bit integer".into());
        }
        let counter = if hotp {
            Some(
                get("counter")
                    .ok_or("HOTP requires a counter")?
                    .parse::<u64>()
                    .map_err(|_| "Invalid HOTP counter")?,
            )
        } else {
            if get("counter").is_some() {
                return Err("TOTP does not accept a counter".into());
            }
            None
        };
        if hotp && get("period").is_some() {
            return Err("HOTP does not accept a period".into());
        }
        // Decode the label without interpreting '+' as a space in a URL path.
        let label_raw = url.path().strip_prefix('/').unwrap_or_default();
        let decoded = percent_label(label_raw)?;
        if decoded.is_empty() {
            return Err("Missing OTP label".into());
        }
        let issuer = get("issuer").unwrap_or("");
        if let Some((prefix, _)) = decoded.split_once(':')
            && !issuer.is_empty()
            && prefix != issuer
        {
            return Err("Issuer does not match the label prefix".into());
        }
        let display = if issuer.is_empty() || decoded.contains(':') {
            decoded
        } else {
            format!("{issuer}:{decoded}")
        };
        let label: String = display
            .chars()
            .filter(|c| !c.is_control())
            .take(120)
            .collect();
        if label.is_empty() {
            return Err("Missing printable OTP label".into());
        }
        Ok(Self {
            label,
            secret,
            algorithm,
            digits,
            period,
            counter,
        })
    }
    fn code(&self, timestamp: u64) -> String {
        let counter = self
            .counter
            .unwrap_or(timestamp / self.period)
            .to_be_bytes();
        macro_rules! digest {
            ($hash:ty) => {{
                let mut mac = Hmac::<$hash>::new_from_slice(&self.secret)
                    .expect("HMAC accepts arbitrary key lengths");
                mac.update(&counter);
                mac.finalize().into_bytes().to_vec()
            }};
        }
        let mut digest = match self.algorithm {
            Algorithm::Sha1 => digest!(Sha1),
            Algorithm::Sha256 => digest!(Sha256),
            Algorithm::Sha512 => digest!(Sha512),
        };
        let offset = (digest[digest.len() - 1] & 15) as usize;
        let binary = u32::from_be_bytes(
            digest[offset..offset + 4]
                .try_into()
                .expect("HMAC output length"),
        ) & 0x7fff_ffff;
        digest.zeroize();
        format!(
            "{:0width$}",
            u64::from(binary) % 10u64.pow(self.digits),
            width = self.digits as usize
        )
    }
}
fn percent_label(text: &str) -> Fallible<String> {
    let mut out = Vec::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            if i + 2 >= bytes.len() {
                return Err("Invalid label encoding".into());
            }
            let hex =
                std::str::from_utf8(&bytes[i + 1..i + 3]).map_err(|_| "Invalid label encoding")?;
            out.push(u8::from_str_radix(hex, 16).map_err(|_| "Invalid label encoding")?);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).map_err(|_| "Label must be UTF-8".into())
}
#[derive(Default)]
pub struct Store {
    entries: RefCell<Vec<Entry>>,
}
pub fn store_new() -> Store {
    Store::default()
}
pub fn count(store: &Store) -> i64 {
    store.entries.borrow().len() as i64
}
pub fn add(store: &Store, uri: &[u8]) -> Fallible<i64> {
    let entry = Entry::parse(uri)?;
    let mut entries = store.entries.borrow_mut();
    if entries.len() >= MAX_ENTRIES {
        return Err("At most 1000 session entries are supported".into());
    }
    entries.push(entry);
    Ok(entries.len() as i64 - 1)
}
fn index(index: i64, length: usize) -> Fallible<usize> {
    usize::try_from(index)
        .ok()
        .filter(|i| *i < length)
        .ok_or_else(|| "No entry selected".into())
}
pub fn remove(store: &Store, at: i64) -> Fallible<()> {
    let mut entries = store.entries.borrow_mut();
    let at = index(at, entries.len())?;
    entries.remove(at);
    Ok(())
}
pub fn label(store: &Store, at: i64) -> Fallible<Vec<u8>> {
    let entries = store.entries.borrow();
    Ok(clip_columns(&entries[index(at, entries.len())?].label, 28).into_bytes())
}
pub fn code(store: &Store, at: i64, timestamp: i64) -> Fallible<Vec<u8>> {
    let timestamp = u64::try_from(timestamp).map_err(|_| "Timestamp must not be negative")?;
    let entries = store.entries.borrow();
    Ok(entries[index(at, entries.len())?]
        .code(timestamp)
        .into_bytes())
}
pub fn remaining(store: &Store, at: i64, timestamp: i64) -> Fallible<i64> {
    let timestamp = u64::try_from(timestamp).map_err(|_| "Timestamp must not be negative")?;
    let entries = store.entries.borrow();
    let entry = &entries[index(at, entries.len())?];
    Ok(if entry.counter.is_some() {
        -1
    } else {
        (entry.period - timestamp % entry.period) as i64
    })
}
pub fn advance(store: &Store, at: i64) -> Fallible<()> {
    let mut entries = store.entries.borrow_mut();
    let at = index(at, entries.len())?;
    let counter = entries[at]
        .counter
        .as_mut()
        .ok_or("Only HOTP entries have a counter")?;
    *counter = counter.checked_add(1).ok_or("HOTP counter exhausted")?;
    Ok(())
}
pub fn now() -> Fallible<i64> {
    i64::try_from(
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| "Clock predates Unix epoch")?
            .as_secs(),
    )
    .map_err(|_| "Clock is out of range".into())
}
pub fn backspace(input: &[u8]) -> Fallible<Vec<u8>> {
    let text = std::str::from_utf8(input).map_err(|_| "Input must be UTF-8")?;
    let mut text = text.to_owned();
    text.pop();
    Ok(text.into_bytes())
}

/// Owns raw mode/alternate screen. Kush's generated release shim runs Drop.
pub struct Terminal {
    active: bool,
}
impl Drop for Terminal {
    fn drop(&mut self) {
        if self.active {
            let _ = execute!(
                io::stdout(),
                event::DisableBracketedPaste,
                cursor::Show,
                LeaveAlternateScreen
            );
            let _ = terminal::disable_raw_mode();
        }
    }
}
pub fn terminal_open() -> Fallible<Terminal> {
    if !io::stdin().is_terminal() || !io::stdout().is_terminal() {
        return Err("Interactive mode requires a terminal; use --help or --code-stdin".into());
    }
    terminal::enable_raw_mode().map_err(|_| "Cannot enable terminal raw mode")?;
    let terminal = Terminal { active: true };
    execute!(
        io::stdout(),
        EnterAlternateScreen,
        cursor::Hide,
        event::EnableBracketedPaste
    )
    .map_err(|_| "Cannot initialize terminal")?;
    Ok(terminal)
}
pub fn terminal_draw(_terminal: &Terminal, frame: &[u8]) -> Fallible<()> {
    let text = std::str::from_utf8(frame).map_err(|_| "Frame must be UTF-8")?;
    let mut out = io::stdout();
    execute!(
        out,
        cursor::MoveTo(0, 0),
        terminal::Clear(terminal::ClearType::All)
    )
    .map_err(|_| "Terminal output failed")?;
    let (columns, rows) = terminal::size().map_err(|_| "Cannot read terminal size")?;
    for (at, line) in text.lines().take(rows as usize).enumerate() {
        if at > 0 {
            write!(out, "\r\n").map_err(|_| "Terminal output failed")?;
        }
        write!(
            out,
            "{}",
            clip_columns(line, columns.saturating_sub(1) as usize)
        )
        .map_err(|_| "Terminal output failed")?;
    }
    out.flush().map_err(|_| "Terminal output failed".into())
}
// Event byte 0 = timeout; 1 = UTF-8 text/paste, bytes after tag are payload;
// 2 enter, 3 escape, 4 backspace, 5 up, 6 down, 7 home, 8 end,
// 9 page-up, 10 page-down, 11 ctrl-c, 12 resize, 13 invalid paste.
pub fn terminal_event(_terminal: &Terminal) -> Fallible<Vec<u8>> {
    if !event::poll(Duration::from_millis(100)).map_err(|_| "Terminal polling failed")? {
        return Ok(vec![0]);
    }
    let bytes = match event::read().map_err(|_| "Terminal input failed")? {
        Event::Key(key) if key.kind != KeyEventKind::Release => match key.code {
            KeyCode::Char('c') if key.modifiers.contains(KeyModifiers::CONTROL) => vec![11],
            KeyCode::Char(c)
                if !key
                    .modifiers
                    .intersects(KeyModifiers::CONTROL | KeyModifiers::ALT)
                    && !c.is_control() =>
            {
                let mut out = vec![1];
                let mut buf = [0; 4];
                out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
                out
            }
            KeyCode::Enter => vec![2],
            KeyCode::Esc => vec![3],
            KeyCode::Backspace => vec![4],
            KeyCode::Up => vec![5],
            KeyCode::Down => vec![6],
            KeyCode::Home => vec![7],
            KeyCode::End => vec![8],
            KeyCode::PageUp => vec![9],
            KeyCode::PageDown => vec![10],
            _ => vec![0],
        },
        Event::Paste(mut text) => {
            let result = if text.len() <= MAX_INPUT && !text.chars().any(char::is_control) {
                let mut out = vec![1];
                out.extend_from_slice(text.as_bytes());
                Ok(out)
            } else {
                Ok(vec![13])
            };
            text.zeroize();
            return result;
        }
        Event::Resize(..) => vec![12],
        _ => vec![0],
    };
    Ok(bytes)
}
pub fn clipboard(terminal: &Terminal, text: &[u8]) -> Fallible<()> {
    let _ = terminal;
    if text.is_empty() || text.len() > 10 || !text.iter().all(u8::is_ascii_digit) {
        return Err("Clipboard accepts only an OTP code".into());
    }
    let text = std::str::from_utf8(text).map_err(|_| "Code must be UTF-8")?;
    execute!(
        io::stdout(),
        crossterm::clipboard::CopyToClipboard::to_clipboard_from(text)
    )
    .map_err(|_| "Clipboard request failed".to_owned())
}
/// Read a URI without putting it in argv/shell history. Headless only.
pub fn read_uri() -> Fallible<Vec<u8>> {
    use std::io::Read;
    if io::stdin().is_terminal() {
        return Err(
            "--code-stdin requires redirected stdin; use interactive mode to paste privately"
                .into(),
        );
    }
    let mut input = Zeroizing::new(Vec::new());
    io::stdin()
        .take(MAX_INPUT as u64 + 1)
        .read_to_end(&mut input)
        .map_err(|_| "Cannot read URI from stdin")?;
    if input.len() > MAX_INPUT {
        return Err("URI exceeds 8192 bytes".into());
    }
    while matches!(input.last(), Some(b'\n' | b'\r')) {
        input.pop();
    }
    Ok(std::mem::take(&mut *input))
}

pub fn report(message: &[u8]) -> Fallible<()> {
    let mut stderr = io::stderr().lock();
    stderr
        .write_all(message)
        .and_then(|()| stderr.write_all(b"\n"))
        .map_err(|_| "Cannot write stderr".to_owned())
}

fn clip_columns(text: &str, limit: usize) -> String {
    let mut width = 0;
    text.chars()
        .take_while(|c| {
            width += c.width().unwrap_or(0);
            width <= limit
        })
        .collect()
}
pub fn terminal_rows(_terminal: &Terminal) -> Fallible<i64> {
    terminal::size()
        .map(|(_, rows)| i64::from(rows))
        .map_err(|_| "Cannot read terminal size".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn uri(kind: &str, secret: &[u8], suffix: &str) -> Vec<u8> {
        format!(
            "otpauth://{kind}/RFC?secret={}{}",
            BASE32_NOPAD.encode(secret),
            suffix
        )
        .into_bytes()
    }
    #[test]
    fn rfc4226_all_counters() {
        let mut entry = Entry::parse(&uri("hotp", b"12345678901234567890", "&counter=0")).unwrap();
        for (counter, expected) in [
            "755224", "287082", "359152", "969429", "338314", "254676", "287922", "162583",
            "399871", "520489",
        ]
        .into_iter()
        .enumerate()
        {
            entry.counter = Some(counter as u64);
            assert_eq!(entry.code(0), expected);
        }
    }
    #[test]
    fn rfc6238_all_hashes_and_large_timestamps() {
        let rows = [
            (59, ["94287082", "46119246", "90693936"]),
            (1111111109, ["07081804", "68084774", "25091201"]),
            (1111111111, ["14050471", "67062674", "99943326"]),
            (1234567890, ["89005924", "91819424", "93441116"]),
            (2000000000, ["69279037", "90698825", "38618901"]),
            (20000000000, ["65353130", "77737706", "47863826"]),
        ];
        for (i, (algorithm, key)) in [
            ("SHA1", "12345678901234567890"),
            ("SHA256", "12345678901234567890123456789012"),
            (
                "SHA512",
                "1234567890123456789012345678901234567890123456789012345678901234",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let entry = Entry::parse(&uri(
                "totp",
                key.as_bytes(),
                &format!("&algorithm={algorithm}&digits=8"),
            ))
            .unwrap();
            for (timestamp, expected) in rows {
                assert_eq!(entry.code(timestamp), expected[i]);
            }
        }
    }
    #[test]
    fn strict_uri_validation_and_no_partial_store_updates() {
        let store = store_new();
        let valid =
            "otpauth://totp/Issuer%3Aalice%40example.com?secret=JBSWY3DPEHPK3PXP&issuer=Issuer";
        add(&store, valid.as_bytes()).unwrap();
        assert_eq!(label(&store, 0).unwrap(), b"Issuer:alice@example.com");
        for text in [
            "",
            "https://totp/A?secret=MY",
            "otpauth://unknown/A?secret=MY",
            "otpauth://totp/A?secret=",
            "otpauth://totp/A?secret=M!",
            "otpauth://totp/A?secret=MY&secret=MY",
            "otpauth://totp/A?secret=MY&digits=5",
            "otpauth://totp/A?secret=MY&digits=11",
            "otpauth://totp/A?secret=MY&period=0",
            "otpauth://totp/A?secret=MY&period=18446744073709551615",
            "otpauth://totp/A?secret=MY&algorithm=MD5",
            "otpauth://hotp/A?secret=MY",
            "otpauth://hotp/A?secret=MY&counter=-1",
            "otpauth://totp/Wrong%3Aa?secret=MY&issuer=Right",
            "otpauth://totp/A%FF?secret=MY",
            "otpauth://totp/A?secret=MY&unknown=true",
            "otpauth://totp/A?secret=MY#fragment",
        ] {
            assert!(add(&store, text.as_bytes()).is_err(), "accepted {text}");
            assert_eq!(count(&store), 1);
        }
        assert!(add(&store, &vec![b'a'; MAX_INPUT + 1]).is_err());
        assert!(code(&store, -1, 59).is_err());
        assert!(code(&store, 0, -1).is_err());
        assert!(remove(&store, 1).is_err());
        assert_eq!(count(&store), 1);
        remove(&store, 0).unwrap();
        assert_eq!(count(&store), 0);
    }
    #[test]
    fn periods_digits_padding_and_counter_exhaustion() {
        let store = store_new();
        let at = add(
            &store,
            b"otpauth://totp/A?secret=MY======&digits=10&period=45",
        )
        .unwrap();
        assert_eq!(code(&store, at, 59).unwrap().len(), 10);
        assert_eq!(remaining(&store, at, 44).unwrap(), 1);
        assert_eq!(remaining(&store, at, 45).unwrap(), 45);
        assert!(advance(&store, at).is_err());
        let at = add(
            &store,
            b"otpauth://hotp/A?secret=my&counter=18446744073709551615",
        )
        .unwrap();
        let before = code(&store, at, 0).unwrap();
        assert!(advance(&store, at).is_err());
        assert_eq!(code(&store, at, 0).unwrap(), before);
    }
    #[test]
    fn labels_cannot_inject_terminal_escapes_and_unicode_backspace_is_valid() {
        let store = store_new();
        add(&store, b"otpauth://totp/A%1B%0A%0DB?secret=MY").unwrap();
        assert_eq!(label(&store, 0).unwrap(), b"AB");
        assert_eq!(backspace("aé😀".as_bytes()).unwrap(), "aé".as_bytes());
        assert_eq!(backspace(&[]).unwrap(), b"");
        assert!(backspace(&[255]).is_err());
    }
}
