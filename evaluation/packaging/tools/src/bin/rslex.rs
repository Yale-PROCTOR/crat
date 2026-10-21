#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_lexer;

use std::{collections::HashSet, env, fs};

use rustc_lexer::{tokenize, TokenKind};

fn is_comment(k: &TokenKind) -> bool {
    matches!(
        k,
        TokenKind::LineComment { .. } | TokenKind::BlockComment { .. }
    )
}

fn strip(src: &str) -> (String, usize) {
    let mut out = String::with_capacity(src.len());
    let mut pos = 0usize;
    let mut n = 0usize;
    let mut touched: HashSet<usize> = HashSet::new();
    let mut out_line = 0usize;
    for t in tokenize(src) {
        let len = t.len as usize;
        let text = &src[pos..pos + len];
        pos += len;
        if is_comment(&t.kind) {
            n += 1;
            touched.insert(out_line);
            if matches!(t.kind, TokenKind::BlockComment { .. }) {
                let prev_nonws = out
                    .chars()
                    .last()
                    .map(|c| !c.is_whitespace())
                    .unwrap_or(false);
                let next_nonws = src[pos..]
                    .chars()
                    .next()
                    .map(|c| !c.is_whitespace())
                    .unwrap_or(false);
                if prev_nonws && next_nonws {
                    out.push(' ');
                }
            }
        } else {
            out.push_str(text);
            out_line += text.matches('\n').count();
        }
    }
    assert_eq!(pos, src.len());
    let mut result = String::with_capacity(out.len());
    for (i, line) in out.split_inclusive('\n').enumerate() {
        if touched.contains(&i) {
            let (body, had_nl) = match line.strip_suffix('\n') {
                Some(b) => (b, true),
                None => (line, false),
            };
            let trimmed = body.trim_end();
            if trimmed.is_empty() {
                continue;
            }
            result.push_str(trimmed);
            if had_nl {
                result.push('\n');
            }
        } else {
            result.push_str(line);
        }
    }
    (result, n)
}

fn dump(src: &str) -> String {
    let mut out = String::new();
    let mut pos = 0usize;
    for t in tokenize(src) {
        let len = t.len as usize;
        let text = &src[pos..pos + len];
        pos += len;
        if is_comment(&t.kind) || matches!(t.kind, TokenKind::Whitespace) {
            continue;
        }
        out.push_str(&format!("{:?}\t{}\n", t.kind, text.replace('\n', "\\n")));
    }
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args[1].as_str();
    for path in &args[2..] {
        let src = fs::read_to_string(path).expect("read");
        match mode {
            "dump" => print!("{}", dump(&src)),
            "count" => {
                let (mut n, mut lines, mut pos) = (0usize, 0usize, 0usize);
                for t in tokenize(&src) {
                    let len = t.len as usize;
                    if is_comment(&t.kind) {
                        n += 1;
                        lines += src[pos..pos + len].trim_end_matches('\n').matches('\n').count() + 1;
                    }
                    pos += len;
                }
                println!("{}\t{}\t{}", path, n, lines);
            }
            "strip" => {
                let (stripped, n) = strip(&src);
                let (again, n2) = strip(&stripped);
                assert_eq!(n2, 0, "second pass found comments in {}", path);
                assert_eq!(again, stripped);
                fs::write(path, &stripped).expect("write");
                println!("{}\t{}\t{}\t{}", path, n, src.len(), stripped.len());
            }
            _ => panic!("mode"),
        }
    }
}
