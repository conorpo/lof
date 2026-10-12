use serde_json::{Value, json};
use std::path::PathBuf;

pub(super) fn file_path(uri: &str) -> Option<PathBuf> {
    let path = uri
        .strip_prefix("file://localhost/")
        .map(|rest| format!("/{rest}"))
        .or_else(|| uri.strip_prefix("file://").map(str::to_owned))?;
    if !path.starts_with('/') {
        return None;
    }
    let bytes = path.as_bytes();
    let mut decoded = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            let hex = std::str::from_utf8(bytes.get(i + 1..i + 3)?).ok()?;
            decoded.push(u8::from_str_radix(hex, 16).ok()?);
            i += 3;
        } else {
            decoded.push(bytes[i]);
            i += 1;
        }
    }
    Some(PathBuf::from(String::from_utf8(decoded).ok()?))
}

pub(super) fn position(source: &str, offset: usize) -> Value {
    let mut offset = offset.min(source.len());
    while !source.is_char_boundary(offset) {
        offset -= 1;
    }
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
    let character = prefix
        .rsplit('\n')
        .next()
        .unwrap_or("")
        .encode_utf16()
        .count();
    json!({"line": line, "character": character})
}

pub(super) fn offset(source: &str, position: &Value) -> usize {
    let line = position["line"].as_u64().unwrap_or(0) as usize;
    let character = position["character"].as_u64().unwrap_or(0) as usize;
    let Some((start, text)) = source
        .split_inclusive('\n')
        .scan(0usize, |start, text| {
            let result = (*start, text);
            *start += text.len();
            Some(result)
        })
        .nth(line)
    else {
        return source.len();
    };
    let mut units = 0;
    for (index, ch) in text.char_indices() {
        if units >= character || ch == '\n' {
            return start + index;
        }
        units += ch.len_utf16();
    }
    start + text.len()
}

pub(super) fn range(source: &str, start: usize, end: usize) -> Value {
    json!({"start": position(source, start), "end": position(source, end)})
}
