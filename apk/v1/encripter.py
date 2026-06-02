#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
All-The-Ciphers — COMPLETE + SmartGuess + BruteForce (Part 1)
This is a single-file toolkit with:
- Classical & polygraphic ciphers
- Encodings & novelty systems
- Tagged formats for reliable round-trips
- Smart English scoring
- SmartGuess dispatcher (detect + decode)
- BruteForce (ranked) for common key spaces

Part 1 includes all cipher/codec implementations and the new
SmartGuess/BruteForce cores. Part 2 will include GUI wiring, CLI,
and extended tests (keep this file name the same).
"""

from __future__ import annotations

import base64
import html
import hashlib
import json
import math
import quopri
import random
import string
import textwrap
import urllib.parse
from typing import List, Tuple, Dict, Iterable, Optional

# GUI & CLI come in Part 2
try:
    import tkinter as tk
    from tkinter import ttk, messagebox
except Exception:
    tk = None
    ttk = None

# =============================================================================
# Core utilities
# =============================================================================

ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
ALPHA_SET = set(ALPHA)
ALNUM = string.ascii_uppercase + string.digits

def to_upper(s: str) -> str:
    return s.upper()

def only_alpha(s: str, keep_spaces: bool = False) -> str:
    s = to_upper(s)
    out = []
    for ch in s:
        if ch in ALPHA_SET:
            out.append(ch)
        elif keep_spaces and ch.isspace():
            out.append(ch)
    return "".join(out)

def alpha_num(s: str, keep_spaces: bool = False) -> str:
    s = to_upper(s)
    out = []
    for ch in s:
        if ch in ALPHA or ch.isdigit():
            out.append(ch)
        elif keep_spaces and ch.isspace():
            out.append(ch)
    return "".join(out)

def chunk(s: str, n: int) -> List[str]:
    return [s[i:i+n] for i in range(0, len(s), n)]

def mod_inv(a: int, m: int) -> int:
    a = a % m
    if a == 0:
        raise ValueError("No inverse for 0")
    t, new_t = 0, 1
    r, new_r = m, a
    while new_r != 0:
        q = r // new_r
        t, new_t = new_t, t - q*new_t
        r, new_r = new_r, r - q*new_r
    if r != 1:
        raise ValueError(f"{a} has no inverse mod {m}")
    return t % m

def key_to_shifts(key: str, alphabet: str = ALPHA) -> List[int]:
    key = only_alpha(key)
    return [alphabet.index(k) for k in key]

def repeat_key_shifts(text_len: int, shifts: List[int]) -> List[int]:
    if not shifts:
        return [0] * text_len
    reps = (text_len + len(shifts) - 1) // len(shifts)
    return (shifts * reps)[:text_len]

def rotate_alpha_from_keyword(keyword: str, alphabet: str = ALPHA) -> str:
    seen = set()
    out = []
    for ch in only_alpha(keyword):
        if ch not in seen:
            out.append(ch); seen.add(ch)
    for ch in alphabet:
        if ch not in seen:
            out.append(ch)
    return "".join(out)

def numeric_order_from_keyword(keyword: str) -> List[int]:
    kw = to_upper(keyword)
    pairs = [(ch, i) for i, ch in enumerate(kw)]
    pairs_sorted = sorted(pairs, key=lambda x: (x[0], x[1]))
    rank = [0] * len(kw)
    for r, (_, i) in enumerate(pairs_sorted):
        rank[i] = r
    return rank

def apply_monoalpha(text: str, src_alpha: str, dst_alpha: str, keep_others: bool = False) -> str:
    table = {s: d for s, d in zip(src_alpha, dst_alpha)}
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in table:
            mapped = table[cu]
            out.append(mapped if ch.isupper() else mapped.lower())
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

# =============================================================================
# Classical shifts / substitutions
# =============================================================================

def Caesar_encode(text: str, shift: int | str = 3, keep_others: bool = True) -> str:
    if isinstance(shift, str): shift = int(shift.strip())
    out = []
    for ch in text:
        if ch.upper() in ALPHA_SET:
            idx = ALPHA.index(ch.upper())
            new = ALPHA[(idx + shift) % 26]
            out.append(new if ch.isupper() else new.lower())
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Caesar_decode(text: str, shift: int | str = 3, keep_others: bool = True) -> str:
    if isinstance(shift, str): shift = int(shift.strip())
    return Caesar_encode(text, -shift, keep_others=keep_others)

def ROT13_encode(text: str) -> str:
    return Caesar_encode(text, 13, keep_others=True)

def ROT13_decode(text: str) -> str:
    return Caesar_encode(text, -13, keep_others=True)

def ROT47_encode(text: str) -> str:
    out = []
    for ch in text:
        o = ord(ch)
        if 33 <= o <= 126:
            out.append(chr(33 + ((o - 33 + 47) % 94)))
        else:
            out.append(ch)
    return "".join(out)

def ROT47_decode(text: str) -> str:
    out = []
    for ch in text:
        o = ord(ch)
        if 33 <= o <= 126:
            out.append(chr(33 + ((o - 33 - 47) % 94)))
        else:
            out.append(ch)
    return "".join(out)

def Atbash_encode(text: str, keep_others: bool = True) -> str:
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            new = ALPHA[25 - ALPHA.index(cu)]
            out.append(new if ch.isupper() else new.lower())
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Atbash_decode(text: str, keep_others: bool = True) -> str:
    return Atbash_encode(text, keep_others=keep_others)

def Affine_encode(text: str, a: int | str = 5, b: int | str = 8, m: int | str = 26, keep_others: bool = True) -> str:
    a = int(a); b = int(b); m = int(m)
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            x = ALPHA.index(cu)
            y = (a * x + b) % m
            new = ALPHA[y]
            out.append(new if ch.isupper() else new.lower())
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Affine_decode(text: str, a: int | str = 5, b: int | str = 8, m: int | str = 26, keep_others: bool = True) -> str:
    a = int(a); b = int(b); m = int(m)
    a_inv = mod_inv(a, m)
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            y = ALPHA.index(cu)
            x = (a_inv * (y - b)) % m
            new = ALPHA[x]
            out.append(new if ch.isupper() else new.lower())
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def KeywordShift_encode(text: str, keyword: str = "CIPHER", keep_others: bool = True) -> str:
    dst = rotate_alpha_from_keyword(keyword)
    return apply_monoalpha(text, ALPHA, dst, keep_others=keep_others)

def KeywordShift_decode(text: str, keyword: str = "CIPHER", keep_others: bool = True) -> str:
    dst = rotate_alpha_from_keyword(keyword)
    return apply_monoalpha(text, dst, ALPHA, keep_others=keep_others)

def KeywordSubstitute_encode(text: str, keyword: str = "CIPHER", keep_others: bool = True) -> str:
    return KeywordShift_encode(text, keyword, keep_others)

def KeywordSubstitute_decode(text: str, keyword: str = "CIPHER", keep_others: bool = True) -> str:
    return KeywordShift_decode(text, keyword, keep_others)

# =============================================================================
# Vigenère family
# =============================================================================

def _vig_core(text: str, key: str, enc: bool, keep_others: bool = True) -> str:
    key_shifts = key_to_shifts(key)
    out = []
    ki = 0
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            s = key_shifts[ki % len(key_shifts)] if key_shifts else 0
            a = ALPHA.index(cu)
            b = (a + s) % 26 if enc else (a - s) % 26
            out.append(ALPHA[b] if ch.isupper() else ALPHA[b].lower())
            ki += 1
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Vigenere_encode(text: str, key: str = "LEMON", keep_others: bool = True) -> str:
    return _vig_core(text, key, True, keep_others)

def Vigenere_decode(text: str, key: str = "LEMON", keep_others: bool = True) -> str:
    return _vig_core(text, key, False, keep_others)

def Autokey_encode(text: str, key: str = "QUEENLY", keep_others: bool = True) -> str:
    stream = list(only_alpha(key))
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            s = ALPHA.index(stream[0]) if stream else 0
            stream = stream[1:] + [cu]
            a = ALPHA.index(cu)
            b = ALPHA[(a + s) % 26]
            out.append(b if ch.isupper() else b.lower())
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Autokey_decode(text: str, key: str = "QUEENLY", keep_others: bool = True) -> str:
    stream = list(only_alpha(key))
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            s = ALPHA.index(stream[0]) if stream else 0
            a = ALPHA.index(cu)
            p = ALPHA[(a - s) % 26]
            out.append(p if ch.isupper() else p.lower())
            stream = stream[1:] + [p]
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Beaufort_encode(text: str, key: str = "FORT", keep_others: bool = True) -> str:
    ks = key_to_shifts(key)
    out = []
    i = 0
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            s = ks[i % len(ks)] if ks else 0
            p = ALPHA.index(cu)
            c = (s - p) % 26
            new = ALPHA[c]
            out.append(new if ch.isupper() else new.lower())
            i += 1
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Beaufort_decode(text: str, key: str = "FORT", keep_others: bool = True) -> str:
    return Beaufort_encode(text, key, keep_others)

def Gronsfeld_encode(text: str, key: str = "314159", keep_others: bool = True) -> str:
    digits = [int(d) for d in key if d.isdigit()]
    out = []
    i = 0
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            s = digits[i % len(digits)] if digits else 0
            a = ALPHA.index(cu)
            b = ALPHA[(a + s) % 26]
            out.append(b if ch.isupper() else b.lower())
            i += 1
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def Gronsfeld_decode(text: str, key: str = "314159", keep_others: bool = True) -> str:
    digits = [int(d) for d in key if d.isdigit()]
    out = []
    i = 0
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            s = digits[i % len(digits)] if digits else 0
            a = ALPHA.index(cu)
            p = ALPHA[(a - s) % 26]
            out.append(p if ch.isupper() else p.lower())
            i += 1
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

# Porta (historic/table are equivalent for this build)
def _porta_shift(ch: str, k: str) -> str:
    k = k.upper()
    if k not in ALPHA_SET or ch.upper() not in ALPHA_SET:
        return ch
    idx = (ALPHA.index(k)) // 2
    left = "ABCDEFGHIJKLM"
    right = "NOPQRSTUVWXYZ"
    lch = ch.upper()
    if lch in left:
        pos = left.index(lch)
        res = right[(pos + idx) % 13]
    else:
        pos = right.index(lch)
        res = left[(pos + idx) % 13]
    return res if ch.isupper() else res.lower()

def PortaHistoric_encode(text: str, key: str = "PORTA", keep_others: bool = True) -> str:
    out = []
    k = only_alpha(key) or "A"
    i = 0
    for ch in text:
        if ch.upper() in ALPHA_SET:
            out.append(_porta_shift(ch, k[i % len(k)]))
            i += 1
        else:
            out.append(ch if keep_others else "")
    return "".join(out)

def PortaHistoric_decode(text: str, key: str = "PORTA", keep_others: bool = True) -> str:
    return PortaHistoric_encode(text, key, keep_others)

PortaTable_encode = PortaHistoric_encode
PortaTable_decode = PortaHistoric_decode

def RunningKey_encode(text: str, key: str = "THENEVERENDINGSTORY", keep_others: bool = True) -> str:
    return Vigenere_encode(text, key, keep_others)

def RunningKey_decode(text: str, key: str = "THENEVERENDINGSTORY", keep_others: bool = True) -> str:
    return Vigenere_decode(text, key, keep_others)

def OTPLetters_encode(text: str, key: str = "XMCKL", keep_others: bool = True) -> str:
    return Vigenere_encode(text, key, keep_others)

def OTPLetters_decode(text: str, key: str = "XMCKL", keep_others: bool = True) -> str:
    return Vigenere_decode(text, key, keep_others)

# =============================================================================
# Fun / novelty
# =============================================================================

def Backslang_encode(text: str) -> str: return text[::-1]
def Backslang_decode(text: str) -> str: return text[::-1]

def Rovarspraket_encode(text: str) -> str:
    vowels = set("AEIOUYaeiouy")
    out = []
    for ch in text:
        if ch.isalpha() and ch not in vowels:
            o = ch + ("o" if ch.islower() else "O") + ch
            out.append(o)
        else:
            out.append(ch)
    return "".join(out)

def Rovarspraket_decode(text: str) -> str:
    vowels = set("AEIOUYaeiouy")
    out = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch.isalpha() and ch not in vowels:
            if i+2 < len(text) and (text[i+1] in "oO") and (text[i+2] == ch):
                out.append(ch); i += 3; continue
        out.append(ch); i += 1
    return "".join(out)

def Tutnese_encode(text: str) -> str:
    rules = {
        'b':'bub', 'c':'cash', 'd':'dud', 'f':'fuf', 'g':'gug', 'h':'hash',
        'j':'jug', 'k':'kuck', 'l':'lul', 'm':'mum', 'n':'nun', 'p':'pup',
        'q':'quack', 'r':'rur', 's':'sus', 't':'tut', 'v':'vuv', 'w':'wack',
        'x':'ex', 'y':'yub', 'z':'zub',
        ' ': ' ', '\t':'\t', '\n':'\n'
    }
    out = []
    for ch in text:
        lower = ch.lower()
        if lower in rules:
            w = rules[lower]
            out.append(w if ch.islower() else w.capitalize())
        elif lower in "aeiou":
            w = f"{lower}yay"
            out.append(w if ch.islower() else w.capitalize())
        else:
            out.append(ch)
    return "[TUT]|" + "".join(out)

def Tutnese_decode(text: str) -> str:
    s = text
    if s.startswith("[TUT]|"):
        s = s[len("[TUT]|"):]
    pairs = {
        'bub':'b','cash':'c','dud':'d','fuf':'f','gug':'g','hash':'h',
        'jug':'j','kuck':'k','lul':'l','mum':'m','nun':'n','pup':'p',
        'quack':'q','rur':'r','sus':'s','tut':'t','vuv':'v','wack':'w',
        'ex':'x','yub':'y','zub':'z'
    }
    i = 0; out = []
    while i < len(s):
        if s[i].isspace():
            out.append(s[i]); i += 1; continue
        matched = False
        for L in (5,4,3,2):
            if i+L <= len(s):
                seg = s[i:i+L]; seg_l = seg.lower()
                if seg_l in pairs:
                    ch = pairs[seg_l]
                    out.append(ch if seg.islower() else ch.upper())
                    i += L; matched = True; break
                if seg_l.endswith("yay") and len(seg_l) == 4 and seg_l[0] in "aeiou":
                    ch = seg_l[0]
                    out.append(ch if seg.islower() else ch.upper())
                    i += L; matched = True; break
        if not matched:
            out.append(s[i]); i += 1
    return "".join(out)

LEET_MAP = {
    'A':'4', 'B':'8', 'C':'<', 'D':'|)', 'E':'3', 'F':'ph', 'G':'6', 'H':'#',
    'I':'1', 'J':']', 'K':'|<', 'L':'1_', 'M':'^^', 'N':'^/', 'O':'0', 'P':'|*',
    'Q':'(,)', 'R':'|2', 'S':'5', 'T':'7', 'U':'(_)', 'V':'\\/', 'W':'\\/\\/',
    'X':'}{', 'Y':'`/', 'Z':'2'
}
REV_LEET = {v:k for k,v in sorted(LEET_MAP.items(), key=lambda kv: -len(kv[1]))}

def LEET_encode(text: str) -> str:
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in LEET_MAP:
            out.append(LEET_MAP[cu])
        else:
            out.append(ch)
    return "[LEET]|" + "".join(out)

def LEET_decode(text: str) -> str:
    s = text
    if s.startswith("[LEET]|"):
        s = s[len("[LEET]|"):]
    out = []
    i = 0
    tokens = sorted(REV_LEET.keys(), key=len, reverse=True)
    while i < len(s):
        matched = False
        for tok in tokens:
            if s.startswith(tok, i):
                out.append(REV_LEET[tok])
                i += len(tok)
                matched = True
                break
        if not matched:
            out.append(s[i].upper() if s[i].isalpha() else s[i])
            i += 1
    return "".join(out).lower()

def KeyboardSub_encode(text: str) -> str:
    line1 = "QWERTYUIOP"
    line2 = "ASDFGHJKL"
    line3 = "ZXCVBNM"
    subs = {}
    for row in (line1, line2, line3):
        for i, ch in enumerate(row):
            subs[ch] = row[(i+1) % len(row)]
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in subs:
            rep = subs[cu]
            out.append(rep if ch.isupper() else rep.lower())
        else:
            out.append(ch)
    return "".join(out)

def KeyboardSub_decode(text: str) -> str:
    line1 = "QWERTYUIOP"
    line2 = "ASDFGHJKL"
    line3 = "ZXCVBNM"
    subs = {}
    for row in (line1, line2, line3):
        for i, ch in enumerate(row):
            subs[row[(i+1) % len(row)]] = ch
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in subs:
            rep = subs[cu]
            out.append(rep if ch.isupper() else rep.lower())
        else:
            out.append(ch)
    return "".join(out)

def KeyboardReversed_encode(text: str) -> str:
    qwerty = "QWERTYUIOPASDFGHJKLZXCVBNM"
    rev = qwerty[::-1]
    return apply_monoalpha(text, qwerty, rev, keep_others=True)

def KeyboardReversed_decode(text: str) -> str:
    qwerty = "QWERTYUIOPASDFGHJKLZXCVBNM"
    rev = qwerty[::-1]
    return apply_monoalpha(text, rev, qwerty, keep_others=True)


A1Z26_SEP = "-"

def A1Z26_encode(text: str) -> str:
    tokens = []
    for ch in text:
        cu = ch.upper()
        if cu in ALPHA_SET:
            tokens.append(str(ALPHA.index(cu) + 1))
        elif ch.isspace():
            tokens.append("/")
        else:
            tokens.append(ch)
    return A1Z26_SEP.join(tokens)

def A1Z26_decode(text: str) -> str:
    normalized = text.replace(",", " ").replace(";", " ").strip()
    if A1Z26_SEP in normalized or "/" in normalized:
        parts = normalized.replace("/", f"{A1Z26_SEP}/{A1Z26_SEP}").split(A1Z26_SEP)
    else:
        parts = normalized.split()
    out = []
    for part in parts:
        part = part.strip()
        if not part:
            continue
        if part == "/":
            out.append(" ")
            continue
        try:
            n = int(part)
            out.append(ALPHA[n - 1] if 1 <= n <= 26 else "")
        except Exception:
            out.append(part)
    return "".join(out).lower()

NATO_WORDS = {
    "A":"Alfa", "B":"Bravo", "C":"Charlie", "D":"Delta", "E":"Echo", "F":"Foxtrot",
    "G":"Golf", "H":"Hotel", "I":"India", "J":"Juliett", "K":"Kilo", "L":"Lima",
    "M":"Mike", "N":"November", "O":"Oscar", "P":"Papa", "Q":"Quebec", "R":"Romeo",
    "S":"Sierra", "T":"Tango", "U":"Uniform", "V":"Victor", "W":"Whiskey", "X":"X-ray",
    "Y":"Yankee", "Z":"Zulu", "0":"Zero", "1":"One", "2":"Two", "3":"Three",
    "4":"Four", "5":"Five", "6":"Six", "7":"Seven", "8":"Eight", "9":"Nine"
}
NATO_REV = {v.upper().replace("-", ""): k for k, v in NATO_WORDS.items()}

def NATO_encode(text: str) -> str:
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in NATO_WORDS:
            out.append(NATO_WORDS[cu])
        elif ch.isspace():
            out.append("/")
        else:
            out.append(ch)
    return " ".join(out)

def NATO_decode(text: str) -> str:
    out = []
    for tok in text.replace("/", " / ").split():
        if tok == "/":
            out.append(" ")
        else:
            out.append(NATO_REV.get(tok.upper().replace("-", ""), tok))
    return "".join(out).lower()

BRAILLE_PATTERNS = {"A": 0x01, "B": 0x03, "C": 0x09, "D": 0x19, "E": 0x11, "F": 0x0B, "G": 0x1B, "H": 0x13, "I": 0x0A, "J": 0x1A, "K": 0x05, "L": 0x07, "M": 0x0D, "N": 0x1D, "O": 0x15, "P": 0x0F, "Q": 0x1F, "R": 0x17, "S": 0x0E, "T": 0x1E, "U": 0x25, "V": 0x27, "W": 0x3A, "X": 0x2D, "Y": 0x3D, "Z": 0x35}
BRAILLE_REV = {chr(0x2800 + v): k for k, v in BRAILLE_PATTERNS.items()}

def BrailleUnicode_encode(text: str) -> str:
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in BRAILLE_PATTERNS:
            out.append(chr(0x2800 + BRAILLE_PATTERNS[cu]))
        elif ch.isspace():
            out.append(" ")
        else:
            out.append(ch)
    return "".join(out)

def BrailleUnicode_decode(text: str) -> str:
    out = []
    for ch in text:
        out.append(BRAILLE_REV.get(ch, " " if ch.isspace() else ch))
    return "".join(out).lower()

# =============================================================================
# Encodings
# =============================================================================

def Binary_encode(text: str) -> str:
    data = text.encode("utf-8")
    return " ".join(format(b, "08b") for b in data)

def Binary_decode(text: str) -> str:
    bits = text.replace("\n", " ").split()
    try:
        data = bytes(int(b, 2) for b in bits)
        return data.decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

def Octal_encode(text: str) -> str:
    data = text.encode("utf-8")
    return " ".join(format(b, "03o") for b in data)

def Octal_decode(text: str) -> str:
    parts = text.replace("\n", " ").split()
    try:
        data = bytes(int(p, 8) for p in parts)
        return data.decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

def Hex_encode(text: str) -> str: return text.encode("utf-8").hex()

def Hex_decode(text: str) -> str:
    try:
        return bytes.fromhex(text.strip()).decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

def Base64_encode(text: str) -> str:
    return base64.b64encode(text.encode("utf-8")).decode("ascii")

def Base64_decode(text: str) -> str:
    try:
        return base64.b64decode(text.encode("ascii")).decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

def A85_encode(text: str) -> str:
    return base64.a85encode(text.encode("utf-8")).decode("ascii")

def A85_decode(text: str) -> str:
    try:
        return base64.a85decode(text.encode("ascii")).decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

def B85_encode(text: str) -> str:
    return base64.b85encode(text.encode("utf-8")).decode("ascii")

def B85_decode(text: str) -> str:
    try:
        return base64.b85decode(text.encode("ascii")).decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

def Base32_encode(text: str) -> str:
    return base64.b32encode(text.encode("utf-8")).decode("ascii")

def Base32_decode(text: str) -> str:
    try:
        return base64.b32decode(text.encode("ascii")).decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

CROCKFORD32_ALPH = "0123456789ABCDEFGHJKMNPQRSTVWXYZ"
CROCKFORD32_REV = {ch: i for i, ch in enumerate(CROCKFORD32_ALPH)}
CROCKFORD32_REV.update({"O": 0, "I": 1, "L": 1})
BASE45_ALPH = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
BASE45_REV = {ch: i for i, ch in enumerate(BASE45_ALPH)}

def Base32Crockford_encode(text: str) -> str:
    data = text.encode("utf-8")
    if not data:
        return ""
    n = int.from_bytes(data, "big")
    out = []
    while n:
        n, r = divmod(n, 32)
        out.append(CROCKFORD32_ALPH[r])
    leading = len(data) - len(data.lstrip(bytes([0])))
    return "0" * leading + ("".join(reversed(out)) or "0")

def Base32Crockford_decode(text: str) -> str:
    s = "".join(ch for ch in text.upper() if ch not in "- \t\r\n")
    if not s:
        return ""
    n = 0
    try:
        for ch in s:
            n = n * 32 + CROCKFORD32_REV[ch]
    except KeyError as e:
        return f"Err:invalid Crockford Base32 character {e.args[0]!r}"
    blen = (n.bit_length() + 7) // 8
    data = n.to_bytes(blen, "big") if blen else b""
    leading = len(s) - len(s.lstrip("0"))
    return (bytes([0]) * leading + data).decode("utf-8", errors="replace")

def Base45_encode(text: str) -> str:
    data = text.encode("utf-8")
    out = []
    i = 0
    while i < len(data):
        if i + 1 < len(data):
            x = data[i] * 256 + data[i + 1]
            e = x // (45 * 45)
            x %= 45 * 45
            d = x // 45
            c = x % 45
            out.extend([BASE45_ALPH[c], BASE45_ALPH[d], BASE45_ALPH[e]])
            i += 2
        else:
            x = data[i]
            out.extend([BASE45_ALPH[x % 45], BASE45_ALPH[x // 45]])
            i += 1
    return "".join(out)

def Base45_decode(text: str) -> str:
    s = "".join(ch for ch in text.strip() if not ch.isspace())
    out = bytearray()
    i = 0
    try:
        while i < len(s):
            if i + 2 < len(s):
                x = BASE45_REV[s[i]] + BASE45_REV[s[i+1]] * 45 + BASE45_REV[s[i+2]] * 45 * 45
                if x > 0xffff:
                    return "Err:invalid Base45 triplet"
                out.extend([(x // 256) & 0xff, x & 0xff])
                i += 3
            elif i + 1 < len(s):
                x = BASE45_REV[s[i]] + BASE45_REV[s[i+1]] * 45
                if x > 0xff:
                    return "Err:invalid Base45 pair"
                out.append(x)
                i += 2
            else:
                return "Err:invalid Base45 length"
    except KeyError as e:
        return f"Err:invalid Base45 character {e.args[0]!r}"
    return bytes(out).decode("utf-8", errors="replace")

def QuotedPrintable_encode(text: str) -> str:
    return quopri.encodestring(text.encode("utf-8"), quotetabs=True).decode("ascii")

def QuotedPrintable_decode(text: str) -> str:
    try:
        return quopri.decodestring(text.encode("ascii")).decode("utf-8", errors="replace")
    except Exception as e:
        return f"Err:{e}"

BASE36_ALPH = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
def Base36_encode(text: str) -> str:
    data = text.encode("utf-8")
    n = int.from_bytes(data, "big")
    if n == 0: return "0"
    out = []
    while n > 0:
        n, r = divmod(n, 36)
        out.append(BASE36_ALPH[r])
    return "".join(reversed(out))

def Base36_decode(text: str) -> str:
    s = text.strip().upper()
    n = 0
    for ch in s:
        n = n*36 + BASE36_ALPH.index(ch)
    blen = (n.bit_length() + 7)//8
    return n.to_bytes(blen, "big").decode("utf-8", errors="replace")

BASE58_ALPH = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def Base58_encode(text: str) -> str:
    data = text.encode("utf-8")
    n = int.from_bytes(data, "big")
    out = []
    if n == 0:
        out.append(BASE58_ALPH[0])
    else:
        while n > 0:
            n, r = divmod(n, 58)
            out.append(BASE58_ALPH[r])
    leading_zeros = len(data) - len(data.lstrip(b"\x00"))
    return "1"*leading_zeros + "".join(reversed(out))

def Base58_decode(text: str) -> str:
    s = text.strip()
    n = 0
    for ch in s:
        n = n*58 + BASE58_ALPH.index(ch)
    out = []
    while n > 0:
        n, r = divmod(n, 256)
        out.append(r)
    out_bytes = bytes(reversed(out))
    leading_ones = len(s) - len(s.lstrip("1"))
    out_bytes = b"\x00"*leading_ones + out_bytes
    return out_bytes.decode("utf-8", errors="replace")

def URL_encode(text: str) -> str: return urllib.parse.quote(text, safe="")
def URL_decode(text: str) -> str:
    try:
        return urllib.parse.unquote(text)
    except Exception as e:
        return f"Err:{e}"

def HTMLEntities_encode(text: str) -> str: return html.escape(text, quote=True)
def HTMLEntities_decode(text: str) -> str: return html.unescape(text)

def UEscapes_encode(text: str) -> str:
    out = []
    for ch in text:
        code = ord(ch)
        if 32 <= code <= 126 and ch not in {'\\'}:
            out.append(ch)
        else:
            if code <= 0xFFFF:
                out.append("\\u%04x" % code)
            else:
                out.append("\\U%08x" % code)
    return "".join(out)

def UEscapes_decode(text: str) -> str:
    try:
        return bytes(text, "utf-8").decode("unicode_escape")
    except Exception as e:
        return f"Err:{e}"

def AsciiShiftHex_encode(text: str, shift: int | str = 1) -> str:
    if isinstance(shift, str): shift = int(shift.strip())
    data = text.encode("utf-8")
    shifted = bytes(((b + shift) % 256) for b in data)
    return shifted.hex()

def AsciiShiftHex_decode(text: str, shift: int | str = 1) -> str:
    if isinstance(shift, str): shift = int(shift.strip())
    try:
        data = bytes.fromhex(text)
    except Exception as e:
        return f"Err:{e}"
    unshifted = bytes(((b - shift) % 256) for b in data)
    return unshifted.decode("utf-8", errors="replace")

DNA_MAP = {0:'A', 1:'C', 2:'G', 3:'T'}
DNA_REV = {'A':0,'C':1,'G':2,'T':3,'a':0,'c':1,'g':2,'t':3}

def DNA_encode(text: str) -> str:
    data = text.encode("utf-8")
    bits = "".join(format(b, "08b") for b in data)
    out = []
    for i in range(0, len(bits), 2):
        pair = bits[i:i+2]
        if len(pair) < 2: pair = pair + "0"
        val = int(pair, 2); out.append(DNA_MAP[val])
    return "".join(out)

def DNA_decode(text: str) -> str:
    vals = []
    for ch in text:
        if ch in DNA_REV:
            vals.append(DNA_REV[ch])
        elif ch.isspace():
            continue
        else:
            return f"Err:invalid base '{ch}'"
    bits = "".join(format(v, "02b") for v in vals)
    if len(bits) % 8 != 0:
        bits = bits[:len(bits) - (len(bits) % 8)]
    data = bytes(int(bits[i:i+8], 2) for i in range(0, len(bits), 8))
    return data.decode("utf-8", errors="replace")

# =============================================================================
# Polybius/Playfair family & transpositions & routes
# =============================================================================

def _key_square_5(keyword: str) -> Tuple[str, Dict[str, Tuple[int,int]], Dict[Tuple[int,int], str]]:
    alpha = "ABCDEFGHIKLMNOPQRSTUVWXYZ"  # I/J merged
    mixed = ""; seen = set()
    for ch in only_alpha(keyword):
        ch = 'I' if ch == 'J' else ch
        if ch not in seen and ch in alpha:
            mixed += ch; seen.add(ch)
    for ch in alpha:
        if ch not in seen:
            mixed += ch
    idx = {}; rev = {}
    for i, ch in enumerate(mixed):
        r, c = divmod(i, 5)
        idx[ch] = (r, c); rev[(r, c)] = ch
    return mixed, idx, rev

def _key_square_6(keyword: str) -> Tuple[str, Dict[str, Tuple[int,int]], Dict[Tuple[int,int], str]]:
    alpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    mixed = ""; seen = set()
    for ch in to_upper(keyword):
        if ch in alpha and ch not in seen:
            mixed += ch; seen.add(ch)
    for ch in alpha:
        if ch not in seen:
            mixed += ch
    idx = {}; rev = {}
    for i, ch in enumerate(mixed):
        r, c = divmod(i, 6)
        idx[ch] = (r, c); rev[(r, c)] = ch
    return mixed, idx, rev

def Polybius_encode(text: str, key: str = "KEYWORD") -> str:
    _, pos, _ = _key_square_5(key)
    out = []
    for ch in to_upper(text):
        if ch == 'J': ch = 'I'
        if ch in pos:
            r, c = pos[ch]; out.append(f"{r+1}{c+1}")
        elif ch.isspace():
            out.append("/")
        else:
            out.append("")
    return " ".join(out).replace(" / ", " / ")

def Polybius_decode(text: str, key: str = "KEYWORD") -> str:
    _, _, rev = _key_square_5(key)
    tokens = text.replace("/", " / ").split()
    out = []
    for t in tokens:
        if t == "/":
            out.append(" ")
        elif len(t) == 2 and t[0].isdigit() and t[1].isdigit():
            r = int(t[0])-1; c = int(t[1])-1
            ch = rev.get((r, c), '')
            out.append(ch)
    return "".join(out).lower()

def _playfair_prepare(text: str) -> List[Tuple[str,str]]:
    s = "".join(('I' if ch=='J' else ch) for ch in only_alpha(text))
    pairs = []; i = 0
    while i < len(s):
        a = s[i]
        if i+1 < len(s):
            b = s[i+1]
            if a == b:
                pairs.append((a, 'X')); i += 1
            else:
                pairs.append((a, b)); i += 2
        else:
            pairs.append((a, 'X')); i += 1
    return pairs

def Playfair_encode(text: str, key: str = "KEYWORD") -> str:
    _, pos, rev = _key_square_5(key)
    pairs = _playfair_prepare(text)
    out = []
    for a, b in pairs:
        ra, ca = pos[a]; rb, cb = pos[b]
        if ra == rb:
            out.append(rev[(ra, (ca+1)%5)])
            out.append(rev[(rb, (cb+1)%5)])
        elif ca == cb:
            out.append(rev[((ra+1)%5, ca)])
            out.append(rev[((rb+1)%5, cb)])
        else:
            out.append(rev[(ra, cb)])
            out.append(rev[(rb, ca)])
    return "".join(out).lower()

def Playfair_decode(text: str, key: str = "KEYWORD") -> str:
    _, pos, rev = _key_square_5(key)
    s = only_alpha(text)
    out = []
    for i in range(0, len(s), 2):
        a = s[i]; b = s[i+1]
        ra, ca = pos[a]; rb, cb = pos[b]
        if ra == rb:
            out.append(rev[(ra, (ca-1)%5)])
            out.append(rev[(rb, (cb-1)%5)])
        elif ca == cb:
            out.append(rev[((ra-1)%5, ca)])
            out.append(rev[((rb-1)%5, cb)])
        else:
            out.append(rev[(ra, cb)])
            out.append(rev[(rb, ca)])
    return "".join(out).lower()

def FourSquare_encode(text: str, key1: str = "EXAMPLE", key2: str = "KEYWORD") -> str:
    normal = "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    sq1, pos1, rev1 = _key_square_5(key1)
    sq2, pos2, rev2 = _key_square_5(key2)
    posN = {ch: divmod(i,5) for i, ch in enumerate(normal)}
    revN = {divmod(i,5): ch for i, ch in enumerate(normal)}
    pairs = _playfair_prepare(text)
    out = []
    for a,b in pairs:
        ra, ca = posN[a]; rb, cb = posN[b]
        out.append(rev1[(ra, cb)])
        out.append(rev2[(rb, ca)])
    return "".join(out).lower()

def FourSquare_decode(text: str, key1: str = "EXAMPLE", key2: str = "KEYWORD") -> str:
    normal = "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    sq1, pos1, rev1 = _key_square_5(key1)
    sq2, pos2, rev2 = _key_square_5(key2)
    posN = {ch: divmod(i,5) for i, ch in enumerate(normal)}
    revN = {divmod(i,5): ch for i, ch in enumerate(normal)}
    s = only_alpha(text)
    out = []
    for i in range(0, len(s), 2):
        a = s[i]; b = s[i+1]
        ra, cb = pos1[a]; rb, ca = pos2[b]
        out.append(revN[(ra, ca)])
        out.append(revN[(rb, cb)])
    return "".join(out).lower()

def TwoSquare_encode(text: str, key1: str = "EXAMPLE", key2: str = "KEYWORD") -> str:
    sqL, posL, revL = _key_square_5(key1)
    sqR, posR, revR = _key_square_5(key2)
    normal = "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    posN = {ch: divmod(i,5) for i, ch in enumerate(normal)}
    pairs = _playfair_prepare(text)
    out = []
    for a,b in pairs:
        ra, ca = posL.get(a, posN[a]); rb, cb = posR.get(b, posN[b])
        out.append(revR[(ra, cb)])
        out.append(revL[(rb, ca)])
    return "".join(out).lower()

def TwoSquare_decode(text: str, key1: str = "EXAMPLE", key2: str = "KEYWORD") -> str:
    sqL, posL, revL = _key_square_5(key1)
    sqR, posR, revR = _key_square_5(key2)
    s = only_alpha(text)
    out = []
    for i in range(0, len(s), 2):
        a = s[i]; b = s[i+1]
        ra, cb = posR[a]; rb, ca = posL[b]
        out.append(revL[(ra, ca)])
        out.append(revR[(rb, cb)])
    return "".join(out).lower()

def _col_order(key: str) -> List[int]:
    return numeric_order_from_keyword(key)

def Columnar_encode(text: str, key: str = "CIPHER") -> str:
    s = "".join(ch for ch in text if not ch.isspace())
    cols = len(key); order = _col_order(key)
    rows = math.ceil(len(s)/cols)
    grid = [[""]*cols for _ in range(rows)]
    i = 0
    for r in range(rows):
        for c in range(cols):
            if i < len(s):
                grid[r][c] = s[i]; i += 1
    out = []
    for ord_val in sorted(set(order)):
        for c, o in sorted([(c, o) for c, o in enumerate(order) if o == ord_val], key=lambda x: x[0]):
            for r in range(rows):
                if grid[r][c] != "":
                    out.append(grid[r][c])
    return "".join(out)

def Columnar_decode(text: str, key: str = "CIPHER") -> str:
    s = text
    cols = len(key); order = _col_order(key)
    rows = math.ceil(len(s)/cols)
    base = len(s) // cols; extra = len(s) % cols
    columns_sorted = []
    for ord_val in sorted(set(order)):
        columns_sorted += [c for c, o in enumerate(order) if o == ord_val]
    counts = {c: base for c in range(cols)}
    for i in range(extra):
        counts[columns_sorted[i]] += 1
    grid_cols = {}; idx = 0
    for c in columns_sorted:
        L = counts[c]; grid_cols[c] = list(s[idx:idx+L]); idx += L
    out = []
    for r in range(rows):
        for c in range(cols):
            if grid_cols[c]:
                out.append(grid_cols[c].pop(0))
    return "".join(out)

def Myszkowski_encode(text: str, key: str = "TOMATO") -> str:
    s = "".join(ch for ch in text if not ch.isspace())
    cols = len(key)
    rows = math.ceil(len(s)/cols)
    grid = [[""]*cols for _ in range(rows)]
    i = 0
    for r in range(rows):
        for c in range(cols):
            if i < len(s):
                grid[r][c] = s[i]; i += 1
    kw = to_upper(key)
    groups: Dict[str, List[int]] = {}
    for i, ch in enumerate(kw):
        groups.setdefault(ch, []).append(i)
    out = []
    for ch in sorted(groups.keys()):
        for c in groups[ch]:
            for r in range(rows):
                if grid[r][c]:
                    out.append(grid[r][c])
    return "".join(out)

def Myszkowski_decode(text: str, key: str = "TOMATO") -> str:
    s = text; cols = len(key); rows = math.ceil(len(s)/cols)
    kw = to_upper(key)
    groups: Dict[str, List[int]] = {}
    for i, ch in enumerate(kw):
        groups.setdefault(ch, []).append(i)
    order_cols = []
    for ch in sorted(groups.keys()):
        order_cols += groups[ch]
    base = len(s)//cols; extra = len(s)%cols
    counts = {c: base for c in range(cols)}
    for i in range(extra):
        counts[order_cols[i]] += 1
    grid_cols = {}; idx = 0
    for c in order_cols:
        L = counts[c]; grid_cols[c] = list(s[idx:idx+L]); idx += L
    out = []
    for r in range(rows):
        for c in range(cols):
            if grid_cols[c]:
                out.append(grid_cols[c].pop(0))
    return "".join(out)

def CaesarBox_encode(text: str, cols: int | str = 4) -> str:
    if isinstance(cols, str): cols = int(cols)
    s = "".join(ch for ch in text if not ch.isspace())
    rows = math.ceil(len(s)/cols)
    grid = [[""]*cols for _ in range(rows)]
    i = 0
    for r in range(rows):
        for c in range(cols):
            if i < len(s):
                grid[r][c] = s[i]; i += 1
    return "".join(grid[r][c] for c in range(cols) for r in range(rows) if grid[r][c] != "")

def CaesarBox_decode(text: str, cols: int | str = 4) -> str:
    if isinstance(cols, str): cols = int(cols)
    s = text; rows = math.ceil(len(s)/cols)
    base = len(s)//cols; extra = len(s)%cols
    col_lengths = [base + (1 if c < extra else 0) for c in range(cols)]
    grid = [[""]*cols for _ in range(rows)]
    idx = 0; cols_data = []
    for c in range(cols):
        L = col_lengths[c]; cols_data.append(list(s[idx:idx+L])); idx += L
    for c in range(cols):
        for r in range(rows):
            if cols_data[c]:
                grid[r][c] = cols_data[c].pop(0)
    return "".join(grid[r][c] for r in range(rows) for c in range(cols) if grid[r][c] != "")

def Scytale_encode(text: str, diameter: int | str = 5) -> str:
    if isinstance(diameter, str): diameter = int(diameter)
    s = "".join(ch for ch in text if not ch.isspace())
    rows = diameter
    cols = math.ceil(len(s)/rows)
    grid = [[""]*cols for _ in range(rows)]
    i = 0
    for c in range(cols):
        for r in range(rows):
            if i < len(s):
                grid[r][c] = s[i]; i += 1
    return "".join(grid[r][c] for r in range(rows) for c in range(cols) if grid[r][c])

def Scytale_decode(text: str, diameter: int | str = 5) -> str:
    if isinstance(diameter, str): diameter = int(diameter)
    s = text; rows = diameter; cols = math.ceil(len(s)/rows)
    base = len(s)//rows; extra = len(s)%rows
    row_lengths = [base + (1 if r < extra else 0) for r in range(rows)]
    rows_data = []; idx = 0
    for r in range(rows):
        L = row_lengths[r]; rows_data.append(list(s[idx:idx+L])); idx += L
    out = []
    for c in range(cols):
        for r in range(rows):
            if rows_data[r]:
                out.append(rows_data[r].pop(0))
    return "".join(out)

def DoubleTransposition_encode(text: str, key1: str = "EXAMPLE", key2: str = "KEYWORD") -> str:
    return Columnar_encode(Columnar_encode(text, key1), key2)

def DoubleTransposition_decode(text: str, key1: str = "EXAMPLE", key2: str = "KEYWORD") -> str:
    return Columnar_decode(Columnar_decode(text, key2), key1)

def Route_encode(text: str, rows: int | str = 5, cols: int | str = 5, route: str = "URDL") -> str:
    if isinstance(rows, str): rows = int(rows)
    if isinstance(cols, str): cols = int(cols)
    s = "".join(ch for ch in text if not ch.isspace())
    L = rows*cols
    s = s.ljust(L, 'X')
    grid = [list(s[r*cols:(r+1)*cols]) for r in range(rows)]
    top, left, bottom, right = 0, 0, rows-1, cols-1
    out = []
    def ring():
        nonlocal top,left,bottom,right
        for c in range(left, right+1): out.append(grid[top][c])
        for r in range(top+1, bottom+1): out.append(grid[r][right])
        if bottom>top:
            for c in range(right-1, left-1, -1): out.append(grid[bottom][c])
        if right>left:
            for r in range(bottom-1, top, -1): out.append(grid[r][left])
        top += 1; left += 1; bottom -= 1; right -= 1
    while top <= bottom and left <= right:
        ring()
    return "".join(out).rstrip('X')

def Route_decode(text: str, rows: int | str = 5, cols: int | str = 5, route: str = "URDL") -> str:
    if isinstance(rows, str): rows = int(rows)
    if isinstance(cols, str): cols = int(cols)
    s = text; L = rows*cols
    s = s.ljust(L, 'X')
    grid = [[""]*cols for _ in range(rows)]
    top, left, bottom, right = 0, 0, rows-1, cols-1
    idx = 0
    while top <= bottom and left <= right:
        for c in range(left, right+1):
            grid[top][c] = s[idx]; idx += 1
        for r in range(top+1, bottom+1):
            grid[r][right] = s[idx]; idx += 1
        if bottom>top:
            for c in range(right-1, left-1, -1):
                grid[bottom][c] = s[idx]; idx += 1
        if right>left:
            for r in range(bottom-1, top, -1):
                grid[r][left] = s[idx]; idx += 1
        top += 1; left += 1; bottom -= 1; right -= 1
    return "".join(grid[r][c] for r in range(rows) for c in range(cols)).rstrip('X')


# =============================================================================
# Extra classical ciphers
# =============================================================================

def ROT5_encode(text: str) -> str:
    out = []
    for ch in text:
        if ch.isdigit():
            out.append(str((int(ch) + 5) % 10))
        else:
            out.append(ch)
    return "".join(out)

def ROT5_decode(text: str) -> str:
    return ROT5_encode(text)

def ROT18_encode(text: str) -> str:
    return ROT5_encode(ROT13_encode(text))

def ROT18_decode(text: str) -> str:
    return ROT18_encode(text)

def _bifid_square(keyword: str = "KEYWORD") -> Tuple[Dict[str, Tuple[int,int]], Dict[Tuple[int,int], str]]:
    _, pos, rev = _key_square_5(keyword)
    return pos, rev

def Bifid_encode(text: str, key: str = "KEYWORD", period: int | str = 5) -> str:
    if isinstance(period, str):
        period = int(period.strip() or "5")
    period = max(1, period)
    pos, rev = _bifid_square(key)
    s = only_alpha(text).replace('J', 'I')
    out = []
    for block in chunk(s, period):
        rows = []
        cols = []
        for ch in block:
            r, c = pos[ch]
            rows.append(r); cols.append(c)
        merged = rows + cols
        for i in range(0, len(merged), 2):
            out.append(rev[(merged[i], merged[i+1])])
    return "".join(out).lower()

def Bifid_decode(text: str, key: str = "KEYWORD", period: int | str = 5) -> str:
    if isinstance(period, str):
        period = int(period.strip() or "5")
    period = max(1, period)
    pos, rev = _bifid_square(key)
    s = only_alpha(text).replace('J', 'I')
    out = []
    for block in chunk(s, period):
        coords = []
        for ch in block:
            coords.extend(pos[ch])
        half = len(block)
        rows = coords[:half]
        cols = coords[half:]
        for r, c in zip(rows, cols):
            out.append(rev[(r, c)])
    return "".join(out).lower()

TRIFID_EXTRA = "."

def _trifid_alphabet(keyword: str = "KEYWORD") -> str:
    seen = set()
    out = []
    for ch in to_upper(keyword):
        if ch in ALPHA_SET or ch == TRIFID_EXTRA:
            if ch not in seen:
                out.append(ch); seen.add(ch)
    for ch in ALPHA + TRIFID_EXTRA:
        if ch not in seen:
            out.append(ch); seen.add(ch)
    return "".join(out[:27])

def _trifid_tables(keyword: str = "KEYWORD") -> Tuple[Dict[str, Tuple[int,int,int]], Dict[Tuple[int,int,int], str]]:
    alpha = _trifid_alphabet(keyword)
    pos: Dict[str, Tuple[int,int,int]] = {}
    rev: Dict[Tuple[int,int,int], str] = {}
    for i, ch in enumerate(alpha):
        layer = i // 9
        rem = i % 9
        row, col = divmod(rem, 3)
        pos[ch] = (layer, row, col)
        rev[(layer, row, col)] = ch
    return pos, rev

def Trifid_encode(text: str, key: str = "KEYWORD", period: int | str = 5) -> str:
    if isinstance(period, str):
        period = int(period.strip() or "5")
    period = max(1, period)
    pos, rev = _trifid_tables(key)
    s = "".join(ch.upper() for ch in text if ch.upper() in ALPHA_SET or ch == TRIFID_EXTRA)
    out = []
    for block in chunk(s, period):
        coords = [[], [], []]
        for ch in block:
            a, b, c = pos[ch]
            coords[0].append(a); coords[1].append(b); coords[2].append(c)
        merged = coords[0] + coords[1] + coords[2]
        for i in range(0, len(merged), 3):
            out.append(rev[(merged[i], merged[i+1], merged[i+2])])
    return "".join(out).lower()

def Trifid_decode(text: str, key: str = "KEYWORD", period: int | str = 5) -> str:
    if isinstance(period, str):
        period = int(period.strip() or "5")
    period = max(1, period)
    pos, rev = _trifid_tables(key)
    s = "".join(ch.upper() for ch in text if ch.upper() in ALPHA_SET or ch == TRIFID_EXTRA)
    out = []
    for block in chunk(s, period):
        flat = []
        for ch in block:
            flat.extend(pos[ch])
        n = len(block)
        a = flat[:n]
        b = flat[n:2*n]
        c = flat[2*n:]
        for coords in zip(a, b, c):
            out.append(rev[coords])
    return "".join(out).lower()

def _parse_hill2_key(key: str) -> Tuple[int, int, int, int]:
    parts = [p.strip() for p in key.replace(";", ",").replace(" ", ",").split(",") if p.strip()]
    if len(parts) == 4:
        nums = tuple(int(p) % 26 for p in parts)
    else:
        letters = only_alpha(key)
        if len(letters) < 4:
            raise ValueError("Hill 2x2 key must be four numbers or at least four letters")
        nums = tuple(ALPHA.index(ch) for ch in letters[:4])
    a, b, c, d = nums
    det = (a*d - b*c) % 26
    mod_inv(det, 26)  # validate invertible
    return a, b, c, d

def Hill2x2_encode(text: str, key: str = "3,3,2,5") -> str:
    a, b, c, d = _parse_hill2_key(key)
    s = only_alpha(text)
    if len(s) % 2:
        s += "X"
    out = []
    for x, y in chunk(s, 2):
        p0 = ALPHA.index(x); p1 = ALPHA.index(y)
        out.append(ALPHA[(a*p0 + b*p1) % 26])
        out.append(ALPHA[(c*p0 + d*p1) % 26])
    return "".join(out).lower()

def Hill2x2_decode(text: str, key: str = "3,3,2,5") -> str:
    a, b, c, d = _parse_hill2_key(key)
    det = (a*d - b*c) % 26
    inv_det = mod_inv(det, 26)
    ia = (d * inv_det) % 26
    ib = (-b * inv_det) % 26
    ic = (-c * inv_det) % 26
    id_ = (a * inv_det) % 26
    s = only_alpha(text)
    if len(s) % 2:
        s += "X"
    out = []
    for x, y in chunk(s, 2):
        c0 = ALPHA.index(x); c1 = ALPHA.index(y)
        out.append(ALPHA[(ia*c0 + ib*c1) % 26])
        out.append(ALPHA[(ic*c0 + id_*c1) % 26])
    return "".join(out).lower()


# =============================================================================
# Modern / recently created ciphers
# =============================================================================

def _xor_stream(data: bytes, stream: Iterable[int]) -> bytes:
    return bytes(b ^ k for b, k in zip(data, stream))

def _rc4_stream(key: bytes) -> Iterable[int]:
    if not key:
        key = bytes([0])
    s = list(range(256))
    j = 0
    for i in range(256):
        j = (j + s[i] + key[i % len(key)]) % 256
        s[i], s[j] = s[j], s[i]
    i = j = 0
    while True:
        i = (i + 1) % 256
        j = (j + s[i]) % 256
        s[i], s[j] = s[j], s[i]
        yield s[(s[i] + s[j]) % 256]

def RC4_hex_encode(text: str, key: str = "secret") -> str:
    data = text.encode("utf-8")
    cipher = _xor_stream(data, _rc4_stream(key.encode("utf-8")))
    return cipher.hex()

def RC4_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    plain = _xor_stream(data, _rc4_stream(key.encode("utf-8")))
    return plain.decode("utf-8", errors="replace")

_SOLITAIRE_JOKER_A = 53
_SOLITAIRE_JOKER_B = 54

def _solitaire_card_value(card: int) -> int:
    return 53 if card in (_SOLITAIRE_JOKER_A, _SOLITAIRE_JOKER_B) else card

def _solitaire_move(deck: List[int], card: int, steps: int) -> None:
    for _ in range(steps):
        i = deck.index(card)
        deck.pop(i)
        new_index = i + 1
        if new_index >= len(deck):
            new_index = 1
        deck.insert(new_index, card)

def _solitaire_triple_cut(deck: List[int]) -> None:
    a = min(deck.index(_SOLITAIRE_JOKER_A), deck.index(_SOLITAIRE_JOKER_B))
    b = max(deck.index(_SOLITAIRE_JOKER_A), deck.index(_SOLITAIRE_JOKER_B))
    deck[:] = deck[b+1:] + deck[a:b+1] + deck[:a]

def _solitaire_count_cut(deck: List[int], count: int) -> None:
    count = count % 54
    if count <= 0 or count >= 53:
        return
    deck[:] = deck[count:-1] + deck[:count] + deck[-1:]

def _solitaire_step(deck: List[int]) -> Optional[int]:
    while True:
        _solitaire_move(deck, _SOLITAIRE_JOKER_A, 1)
        _solitaire_move(deck, _SOLITAIRE_JOKER_B, 2)
        _solitaire_triple_cut(deck)
        _solitaire_count_cut(deck, _solitaire_card_value(deck[-1]))
        top = _solitaire_card_value(deck[0])
        card = deck[top]
        if card not in (_SOLITAIRE_JOKER_A, _SOLITAIRE_JOKER_B):
            return ((card - 1) % 26) + 1

def _solitaire_keyed_deck(key: str) -> List[int]:
    deck = list(range(1, 55))
    for ch in only_alpha(key):
        _solitaire_step(deck)
        _solitaire_count_cut(deck, ALPHA.index(ch) + 1)
    return deck

def Solitaire_encode(text: str, key: str = "CRYPTONOMICON") -> str:
    deck = _solitaire_keyed_deck(key)
    out = []
    for ch in only_alpha(text):
        p = ALPHA.index(ch) + 1
        k = _solitaire_step(deck) or 0
        out.append(ALPHA[(p + k - 1) % 26])
    return "".join(out).lower()

def Solitaire_decode(text: str, key: str = "CRYPTONOMICON") -> str:
    deck = _solitaire_keyed_deck(key)
    out = []
    for ch in only_alpha(text):
        c = ALPHA.index(ch) + 1
        k = _solitaire_step(deck) or 0
        out.append(ALPHA[(c - k - 1) % 26])
    return "".join(out).lower()

def _rotl32(v: int, n: int) -> int:
    return ((v << n) & 0xffffffff) | (v >> (32 - n))

def _quarter_round(state: List[int], a: int, b: int, c: int, d: int) -> None:
    state[a] = (state[a] + state[b]) & 0xffffffff; state[d] ^= state[a]; state[d] = _rotl32(state[d], 16)
    state[c] = (state[c] + state[d]) & 0xffffffff; state[b] ^= state[c]; state[b] = _rotl32(state[b], 12)
    state[a] = (state[a] + state[b]) & 0xffffffff; state[d] ^= state[a]; state[d] = _rotl32(state[d], 8)
    state[c] = (state[c] + state[d]) & 0xffffffff; state[b] ^= state[c]; state[b] = _rotl32(state[b], 7)

def _le_words(data: bytes) -> List[int]:
    return [int.from_bytes(data[i:i+4], "little") for i in range(0, len(data), 4)]

def _parse_chacha_nonce(nonce: str) -> bytes:
    s = str(nonce).strip()
    try:
        raw = bytes.fromhex(s)
        if len(raw) == 12:
            return raw
    except Exception:
        pass
    return hashlib.sha256(s.encode("utf-8")).digest()[:12]

def _chacha_key(key: str) -> bytes:
    return hashlib.sha256(key.encode("utf-8")).digest()

def _chacha20_block(key32: bytes, counter: int, nonce12: bytes) -> bytes:
    constants = b"expand 32-byte k"
    state = _le_words(constants) + _le_words(key32) + [counter & 0xffffffff] + _le_words(nonce12)
    working = state[:]
    for _ in range(10):
        _quarter_round(working, 0, 4, 8, 12)
        _quarter_round(working, 1, 5, 9, 13)
        _quarter_round(working, 2, 6, 10, 14)
        _quarter_round(working, 3, 7, 11, 15)
        _quarter_round(working, 0, 5, 10, 15)
        _quarter_round(working, 1, 6, 11, 12)
        _quarter_round(working, 2, 7, 8, 13)
        _quarter_round(working, 3, 4, 9, 14)
    return b"".join(((working[i] + state[i]) & 0xffffffff).to_bytes(4, "little") for i in range(16))

def _chacha20_stream(key32: bytes, nonce12: bytes, counter: int = 1) -> Iterable[int]:
    block_counter = int(counter)
    while True:
        for b in _chacha20_block(key32, block_counter, nonce12):
            yield b
        block_counter = (block_counter + 1) & 0xffffffff

def ChaCha20_hex_encode(text: str, key: str = "secret", nonce: str = "000000000000000000000000", counter: int | str = 1) -> str:
    counter = int(counter)
    nonce_bytes = _parse_chacha_nonce(nonce)
    cipher = _xor_stream(text.encode("utf-8"), _chacha20_stream(_chacha_key(key), nonce_bytes, counter))
    meta = {"nonce": nonce_bytes.hex(), "counter": counter}
    return "[CHACHA20]" + json.dumps(meta) + "|" + cipher.hex()

def ChaCha20_hex_decode(text: str, key: str = "secret", nonce: str = "000000000000000000000000", counter: int | str = 1) -> str:
    body = text.strip()
    if body.startswith("[CHACHA20]"):
        try:
            meta_end = body.index("|", len("[CHACHA20]"))
            meta = json.loads(body[len("[CHACHA20]"):meta_end])
            nonce = meta.get("nonce", nonce)
            counter = meta.get("counter", counter)
            body = body[meta_end+1:]
        except Exception as e:
            return f"Err:{e}"
    try:
        data = bytes.fromhex(body)
    except Exception as e:
        return f"Err:{e}"
    nonce_bytes = _parse_chacha_nonce(str(nonce))
    plain = _xor_stream(data, _chacha20_stream(_chacha_key(key), nonce_bytes, int(counter)))
    return plain.decode("utf-8", errors="replace")


def _parse_salsa_nonce(nonce: str) -> bytes:
    s = str(nonce).strip()
    try:
        raw = bytes.fromhex(s)
        if len(raw) == 8:
            return raw
    except Exception:
        pass
    return hashlib.sha256(s.encode("utf-8")).digest()[:8]

def _salsa20_quarter_round(state: List[int], a: int, b: int, c: int, d: int) -> None:
    state[b] ^= _rotl32((state[a] + state[d]) & 0xffffffff, 7)
    state[c] ^= _rotl32((state[b] + state[a]) & 0xffffffff, 9)
    state[d] ^= _rotl32((state[c] + state[b]) & 0xffffffff, 13)
    state[a] ^= _rotl32((state[d] + state[c]) & 0xffffffff, 18)

def _salsa20_block(key32: bytes, nonce8: bytes, counter: int) -> bytes:
    constants = b"expand 32-byte k"
    c = _le_words(constants)
    k = _le_words(key32)
    n = _le_words(nonce8)
    state = [c[0], k[0], k[1], k[2], k[3], c[1], n[0], n[1], counter & 0xffffffff, (counter >> 32) & 0xffffffff, c[2], k[4], k[5], k[6], k[7], c[3]]
    working = state[:]
    for _ in range(10):
        _salsa20_quarter_round(working, 0, 4, 8, 12)
        _salsa20_quarter_round(working, 5, 9, 13, 1)
        _salsa20_quarter_round(working, 10, 14, 2, 6)
        _salsa20_quarter_round(working, 15, 3, 7, 11)
        _salsa20_quarter_round(working, 0, 1, 2, 3)
        _salsa20_quarter_round(working, 5, 6, 7, 4)
        _salsa20_quarter_round(working, 10, 11, 8, 9)
        _salsa20_quarter_round(working, 15, 12, 13, 14)
    return b"".join(((working[i] + state[i]) & 0xffffffff).to_bytes(4, "little") for i in range(16))

def _salsa20_stream(key32: bytes, nonce8: bytes, counter: int = 0) -> Iterable[int]:
    block_counter = int(counter)
    while True:
        for b in _salsa20_block(key32, nonce8, block_counter):
            yield b
        block_counter = (block_counter + 1) & 0xffffffffffffffff

def Salsa20_hex_encode(text: str, key: str = "secret", nonce: str = "0000000000000000", counter: int | str = 0) -> str:
    counter = int(counter)
    nonce_bytes = _parse_salsa_nonce(nonce)
    cipher = _xor_stream(text.encode("utf-8"), _salsa20_stream(_chacha_key(key), nonce_bytes, counter))
    meta = {"nonce": nonce_bytes.hex(), "counter": counter}
    return "[SALSA20]" + json.dumps(meta) + "|" + cipher.hex()

def Salsa20_hex_decode(text: str, key: str = "secret", nonce: str = "0000000000000000", counter: int | str = 0) -> str:
    body = text.strip()
    if body.startswith("[SALSA20]"):
        try:
            meta_end = body.index("|", len("[SALSA20]"))
            meta = json.loads(body[len("[SALSA20]"):meta_end])
            nonce = meta.get("nonce", nonce)
            counter = meta.get("counter", counter)
            body = body[meta_end+1:]
        except Exception as e:
            return f"Err:{e}"
    try:
        data = bytes.fromhex(body)
    except Exception as e:
        return f"Err:{e}"
    plain = _xor_stream(data, _salsa20_stream(_chacha_key(key), _parse_salsa_nonce(str(nonce)), int(counter)))
    return plain.decode("utf-8", errors="replace")

def _bytes_to_u32_list(data: bytes, include_length: bool) -> List[int]:
    n = len(data)
    if n % 4:
        data += bytes(4 - (n % 4))
    values = [int.from_bytes(data[i:i+4], "little") for i in range(0, len(data), 4)]
    if include_length:
        values.append(n)
    return values

def _u32_list_to_bytes(values: List[int], include_length: bool) -> bytes:
    if include_length:
        if not values:
            return b""
        n = values[-1]
        values = values[:-1]
    else:
        n = len(values) * 4
    data = b"".join((v & 0xffffffff).to_bytes(4, "little") for v in values)
    return data[:n]

def _xxtea_key(key: str) -> List[int]:
    digest = hashlib.md5(key.encode("utf-8")).digest()
    return [int.from_bytes(digest[i:i+4], "little") for i in range(0, 16, 4)]

def _xxtea_encrypt_words(v: List[int], k: List[int]) -> List[int]:
    n = len(v)
    if n < 2:
        return v
    delta = 0x9E3779B9
    rounds = 6 + 52 // n
    total = 0
    z = v[-1]
    for _ in range(rounds):
        total = (total + delta) & 0xffffffff
        e = (total >> 2) & 3
        for p_idx in range(n - 1):
            y = v[p_idx + 1]
            mx = (((z >> 5) ^ (y << 2)) + ((y >> 3) ^ (z << 4))) ^ ((total ^ y) + (k[(p_idx & 3) ^ e] ^ z))
            mx &= 0xffffffff
            v[p_idx] = (v[p_idx] + mx) & 0xffffffff
            z = v[p_idx]
        y = v[0]
        mx = (((z >> 5) ^ (y << 2)) + ((y >> 3) ^ (z << 4))) ^ ((total ^ y) + (k[((n - 1) & 3) ^ e] ^ z))
        mx &= 0xffffffff
        v[-1] = (v[-1] + mx) & 0xffffffff
        z = v[-1]
    return v

def _xxtea_decrypt_words(v: List[int], k: List[int]) -> List[int]:
    n = len(v)
    if n < 2:
        return v
    delta = 0x9E3779B9
    rounds = 6 + 52 // n
    total = (rounds * delta) & 0xffffffff
    y = v[0]
    while total:
        e = (total >> 2) & 3
        for p_idx in range(n - 1, 0, -1):
            z = v[p_idx - 1]
            mx = (((z >> 5) ^ (y << 2)) + ((y >> 3) ^ (z << 4))) ^ ((total ^ y) + (k[(p_idx & 3) ^ e] ^ z))
            mx &= 0xffffffff
            v[p_idx] = (v[p_idx] - mx) & 0xffffffff
            y = v[p_idx]
        z = v[-1]
        mx = (((z >> 5) ^ (y << 2)) + ((y >> 3) ^ (z << 4))) ^ ((total ^ y) + (k[e] ^ z))
        mx &= 0xffffffff
        v[0] = (v[0] - mx) & 0xffffffff
        y = v[0]
        total = (total - delta) & 0xffffffff
    return v

def XXTEA_hex_encode(text: str, key: str = "secret") -> str:
    values = _bytes_to_u32_list(text.encode("utf-8"), True)
    encrypted = _xxtea_encrypt_words(values[:], _xxtea_key(key))
    return _u32_list_to_bytes(encrypted, False).hex()

def XXTEA_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    values = _bytes_to_u32_list(data, False)
    decrypted = _xxtea_decrypt_words(values, _xxtea_key(key))
    return _u32_list_to_bytes(decrypted, True).decode("utf-8", errors="replace")

def _rotr16(v: int, n: int) -> int:
    return ((v >> n) | ((v << (16 - n)) & 0xffff)) & 0xffff

def _rotl16(v: int, n: int) -> int:
    return (((v << n) & 0xffff) | (v >> (16 - n))) & 0xffff

def _speck32_key_schedule(key: str) -> List[int]:
    digest = hashlib.sha256(key.encode("utf-8")).digest()[:8]
    words = [int.from_bytes(digest[i:i+2], "little") for i in range(0, 8, 2)]
    round_keys = [words[0]]
    l = words[1:]
    for i in range(21):
        new_l = ((_rotr16(l[i], 7) + round_keys[i]) & 0xffff) ^ i
        l.append(new_l)
        round_keys.append(_rotl16(round_keys[i], 2) ^ new_l)
    return round_keys

def _speck32_encrypt_block(block: bytes, round_keys: List[int]) -> bytes:
    x = int.from_bytes(block[:2], "little")
    y = int.from_bytes(block[2:], "little")
    for k in round_keys:
        x = ((_rotr16(x, 7) + y) & 0xffff) ^ k
        y = _rotl16(y, 2) ^ x
    return x.to_bytes(2, "little") + y.to_bytes(2, "little")

def _speck32_decrypt_block(block: bytes, round_keys: List[int]) -> bytes:
    x = int.from_bytes(block[:2], "little")
    y = int.from_bytes(block[2:], "little")
    for k in reversed(round_keys):
        y = _rotr16(y ^ x, 2)
        x = _rotl16(((x ^ k) - y) & 0xffff, 7)
    return x.to_bytes(2, "little") + y.to_bytes(2, "little")

def Speck32_hex_encode(text: str, key: str = "secret") -> str:
    data = len(text.encode("utf-8")).to_bytes(4, "little") + text.encode("utf-8")
    if len(data) % 4:
        data += bytes(4 - (len(data) % 4))
    round_keys = _speck32_key_schedule(key)
    return b"".join(_speck32_encrypt_block(data[i:i+4], round_keys) for i in range(0, len(data), 4)).hex()

def Speck32_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    if len(data) % 4:
        return "Err:ciphertext length must be a multiple of 4 bytes"
    round_keys = _speck32_key_schedule(key)
    plain = b"".join(_speck32_decrypt_block(data[i:i+4], round_keys) for i in range(0, len(data), 4))
    if len(plain) < 4:
        return ""
    n = int.from_bytes(plain[:4], "little")
    return plain[4:4+n].decode("utf-8", errors="replace")


def _tea_key(key: str) -> List[int]:
    digest = hashlib.sha256(key.encode("utf-8")).digest()[:16]
    return [int.from_bytes(digest[i:i+4], "little") for i in range(0, 16, 4)]

def _u32_pair_blocks(text: str, block_size: int = 8) -> bytes:
    data = len(text.encode("utf-8")).to_bytes(4, "little") + text.encode("utf-8")
    if len(data) % block_size:
        data += bytes(block_size - (len(data) % block_size))
    return data

def _decode_length_prefixed(data: bytes) -> str:
    if len(data) < 4:
        return ""
    n = int.from_bytes(data[:4], "little")
    return data[4:4+n].decode("utf-8", errors="replace")

def _tea_encrypt_block(block: bytes, k: List[int]) -> bytes:
    v0 = int.from_bytes(block[:4], "little")
    v1 = int.from_bytes(block[4:], "little")
    total = 0
    delta = 0x9E3779B9
    for _ in range(32):
        total = (total + delta) & 0xffffffff
        v0 = (v0 + ((((v1 << 4) & 0xffffffff) + k[0]) ^ (v1 + total) ^ ((v1 >> 5) + k[1]))) & 0xffffffff
        v1 = (v1 + ((((v0 << 4) & 0xffffffff) + k[2]) ^ (v0 + total) ^ ((v0 >> 5) + k[3]))) & 0xffffffff
    return v0.to_bytes(4, "little") + v1.to_bytes(4, "little")

def _tea_decrypt_block(block: bytes, k: List[int]) -> bytes:
    v0 = int.from_bytes(block[:4], "little")
    v1 = int.from_bytes(block[4:], "little")
    delta = 0x9E3779B9
    total = (delta * 32) & 0xffffffff
    for _ in range(32):
        v1 = (v1 - ((((v0 << 4) & 0xffffffff) + k[2]) ^ (v0 + total) ^ ((v0 >> 5) + k[3]))) & 0xffffffff
        v0 = (v0 - ((((v1 << 4) & 0xffffffff) + k[0]) ^ (v1 + total) ^ ((v1 >> 5) + k[1]))) & 0xffffffff
        total = (total - delta) & 0xffffffff
    return v0.to_bytes(4, "little") + v1.to_bytes(4, "little")

def TEA_hex_encode(text: str, key: str = "secret") -> str:
    data = _u32_pair_blocks(text)
    k = _tea_key(key)
    return b"".join(_tea_encrypt_block(data[i:i+8], k) for i in range(0, len(data), 8)).hex()

def TEA_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    if len(data) % 8:
        return "Err:ciphertext length must be a multiple of 8 bytes"
    k = _tea_key(key)
    plain = b"".join(_tea_decrypt_block(data[i:i+8], k) for i in range(0, len(data), 8))
    return _decode_length_prefixed(plain)

def _xtea_encrypt_block(block: bytes, k: List[int]) -> bytes:
    v0 = int.from_bytes(block[:4], "little")
    v1 = int.from_bytes(block[4:], "little")
    total = 0
    delta = 0x9E3779B9
    for _ in range(32):
        v0 = (v0 + ((((v1 << 4) ^ (v1 >> 5)) + v1) ^ (total + k[total & 3]))) & 0xffffffff
        total = (total + delta) & 0xffffffff
        v1 = (v1 + ((((v0 << 4) ^ (v0 >> 5)) + v0) ^ (total + k[(total >> 11) & 3]))) & 0xffffffff
    return v0.to_bytes(4, "little") + v1.to_bytes(4, "little")

def _xtea_decrypt_block(block: bytes, k: List[int]) -> bytes:
    v0 = int.from_bytes(block[:4], "little")
    v1 = int.from_bytes(block[4:], "little")
    delta = 0x9E3779B9
    total = (delta * 32) & 0xffffffff
    for _ in range(32):
        v1 = (v1 - ((((v0 << 4) ^ (v0 >> 5)) + v0) ^ (total + k[(total >> 11) & 3]))) & 0xffffffff
        total = (total - delta) & 0xffffffff
        v0 = (v0 - ((((v1 << 4) ^ (v1 >> 5)) + v1) ^ (total + k[total & 3]))) & 0xffffffff
    return v0.to_bytes(4, "little") + v1.to_bytes(4, "little")

def XTEA_hex_encode(text: str, key: str = "secret") -> str:
    data = _u32_pair_blocks(text)
    k = _tea_key(key)
    return b"".join(_xtea_encrypt_block(data[i:i+8], k) for i in range(0, len(data), 8)).hex()

def XTEA_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    if len(data) % 8:
        return "Err:ciphertext length must be a multiple of 8 bytes"
    k = _tea_key(key)
    plain = b"".join(_xtea_decrypt_block(data[i:i+8], k) for i in range(0, len(data), 8))
    return _decode_length_prefixed(plain)

def _rotl32_var(v: int, n: int) -> int:
    n &= 31
    return ((v << n) & 0xffffffff) | (v >> ((32 - n) & 31)) if n else v & 0xffffffff

def _rotr32_var(v: int, n: int) -> int:
    n &= 31
    return (v >> n) | ((v << ((32 - n) & 31)) & 0xffffffff) if n else v & 0xffffffff

def _rc5_key_schedule(key: str, rounds: int = 12) -> List[int]:
    key_bytes = hashlib.sha256(key.encode("utf-8")).digest()[:16]
    words = [0] * 4
    for i in range(len(key_bytes) - 1, -1, -1):
        words[i // 4] = ((words[i // 4] << 8) + key_bytes[i]) & 0xffffffff
    s = [0] * (2 * (rounds + 1))
    s[0] = 0xB7E15163
    for i in range(1, len(s)):
        s[i] = (s[i - 1] + 0x9E3779B9) & 0xffffffff
    a = b = i = j = 0
    for _ in range(3 * max(len(words), len(s))):
        a = s[i] = _rotl32_var((s[i] + a + b) & 0xffffffff, 3)
        b = words[j] = _rotl32_var((words[j] + a + b) & 0xffffffff, (a + b) & 31)
        i = (i + 1) % len(s)
        j = (j + 1) % len(words)
    return s

def _rc5_encrypt_block(block: bytes, s: List[int], rounds: int = 12) -> bytes:
    a = int.from_bytes(block[:4], "little")
    b = int.from_bytes(block[4:], "little")
    a = (a + s[0]) & 0xffffffff
    b = (b + s[1]) & 0xffffffff
    for i in range(1, rounds + 1):
        a = (_rotl32_var(a ^ b, b) + s[2 * i]) & 0xffffffff
        b = (_rotl32_var(b ^ a, a) + s[2 * i + 1]) & 0xffffffff
    return a.to_bytes(4, "little") + b.to_bytes(4, "little")

def _rc5_decrypt_block(block: bytes, s: List[int], rounds: int = 12) -> bytes:
    a = int.from_bytes(block[:4], "little")
    b = int.from_bytes(block[4:], "little")
    for i in range(rounds, 0, -1):
        b = _rotr32_var((b - s[2 * i + 1]) & 0xffffffff, a) ^ a
        a = _rotr32_var((a - s[2 * i]) & 0xffffffff, b) ^ b
    b = (b - s[1]) & 0xffffffff
    a = (a - s[0]) & 0xffffffff
    return a.to_bytes(4, "little") + b.to_bytes(4, "little")

def RC5_32_hex_encode(text: str, key: str = "secret") -> str:
    data = _u32_pair_blocks(text)
    s = _rc5_key_schedule(key)
    return b"".join(_rc5_encrypt_block(data[i:i+8], s) for i in range(0, len(data), 8)).hex()

def RC5_32_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    if len(data) % 8:
        return "Err:ciphertext length must be a multiple of 8 bytes"
    s = _rc5_key_schedule(key)
    plain = b"".join(_rc5_decrypt_block(data[i:i+8], s) for i in range(0, len(data), 8))
    return _decode_length_prefixed(plain)


def _chacha_block_rounds(key32: bytes, counter: int, nonce12: bytes, rounds: int) -> bytes:
    constants = b"expand 32-byte k"
    state = _le_words(constants) + _le_words(key32) + [counter & 0xffffffff] + _le_words(nonce12)
    working = state[:]
    for _ in range(rounds // 2):
        _quarter_round(working, 0, 4, 8, 12)
        _quarter_round(working, 1, 5, 9, 13)
        _quarter_round(working, 2, 6, 10, 14)
        _quarter_round(working, 3, 7, 11, 15)
        _quarter_round(working, 0, 5, 10, 15)
        _quarter_round(working, 1, 6, 11, 12)
        _quarter_round(working, 2, 7, 8, 13)
        _quarter_round(working, 3, 4, 9, 14)
    return b"".join(((working[i] + state[i]) & 0xffffffff).to_bytes(4, "little") for i in range(16))

def _chacha_stream_rounds(key32: bytes, nonce12: bytes, counter: int, rounds: int) -> Iterable[int]:
    block_counter = int(counter)
    while True:
        for b in _chacha_block_rounds(key32, block_counter, nonce12, rounds):
            yield b
        block_counter = (block_counter + 1) & 0xffffffff

def _chacha_variant_encode(text: str, key: str, nonce: str, counter: int | str, rounds: int, tag: str) -> str:
    counter = int(counter)
    nonce_bytes = _parse_chacha_nonce(nonce)
    cipher = _xor_stream(text.encode("utf-8"), _chacha_stream_rounds(_chacha_key(key), nonce_bytes, counter, rounds))
    meta = {"nonce": nonce_bytes.hex(), "counter": counter, "rounds": rounds}
    return f"[{tag}]" + json.dumps(meta) + "|" + cipher.hex()

def _chacha_variant_decode(text: str, key: str, nonce: str, counter: int | str, rounds: int, tag: str) -> str:
    body = text.strip()
    prefix = f"[{tag}]"
    if body.startswith(prefix):
        try:
            meta_end = body.index("|", len(prefix))
            meta = json.loads(body[len(prefix):meta_end])
            nonce = meta.get("nonce", nonce)
            counter = meta.get("counter", counter)
            body = body[meta_end+1:]
        except Exception as e:
            return f"Err:{e}"
    try:
        data = bytes.fromhex(body)
    except Exception as e:
        return f"Err:{e}"
    plain = _xor_stream(data, _chacha_stream_rounds(_chacha_key(key), _parse_chacha_nonce(str(nonce)), int(counter), rounds))
    return plain.decode("utf-8", errors="replace")

def ChaCha12_hex_encode(text: str, key: str = "secret", nonce: str = "000000000000000000000000", counter: int | str = 1) -> str:
    return _chacha_variant_encode(text, key, nonce, counter, 12, "CHACHA12")

def ChaCha12_hex_decode(text: str, key: str = "secret", nonce: str = "000000000000000000000000", counter: int | str = 1) -> str:
    return _chacha_variant_decode(text, key, nonce, counter, 12, "CHACHA12")

def ChaCha8_hex_encode(text: str, key: str = "secret", nonce: str = "000000000000000000000000", counter: int | str = 1) -> str:
    return _chacha_variant_encode(text, key, nonce, counter, 8, "CHACHA8")

def ChaCha8_hex_decode(text: str, key: str = "secret", nonce: str = "000000000000000000000000", counter: int | str = 1) -> str:
    return _chacha_variant_decode(text, key, nonce, counter, 8, "CHACHA8")

def _simon_f(x: int) -> int:
    return (_rotl16(x, 1) & _rotl16(x, 8)) ^ _rotl16(x, 2)

def _simon32_key_schedule(key: str) -> List[int]:
    digest = hashlib.sha256(key.encode("utf-8")).digest()[:8]
    keys = [int.from_bytes(digest[i:i+2], "little") for i in range(0, 8, 2)]
    z0 = "11111010001001010110000111001101111101000100101011000011100110"
    for i in range(28):
        tmp = _rotr16(keys[i + 3], 3) ^ keys[i + 1]
        tmp ^= _rotr16(tmp, 1)
        zbit = int(z0[i % len(z0)])
        keys.append((0xfffc ^ zbit ^ keys[i] ^ tmp) & 0xffff)
    return keys[:32]

def _simon32_encrypt_block(block: bytes, round_keys: List[int]) -> bytes:
    x = int.from_bytes(block[:2], "little")
    y = int.from_bytes(block[2:], "little")
    for k in round_keys:
        x, y = (y ^ _simon_f(x) ^ k) & 0xffff, x
    return x.to_bytes(2, "little") + y.to_bytes(2, "little")

def _simon32_decrypt_block(block: bytes, round_keys: List[int]) -> bytes:
    x = int.from_bytes(block[:2], "little")
    y = int.from_bytes(block[2:], "little")
    for k in reversed(round_keys):
        x, y = y, (x ^ _simon_f(y) ^ k) & 0xffff
    return x.to_bytes(2, "little") + y.to_bytes(2, "little")

def Simon32_64_hex_encode(text: str, key: str = "secret") -> str:
    data = _u32_pair_blocks(text, block_size=4)
    round_keys = _simon32_key_schedule(key)
    return b"".join(_simon32_encrypt_block(data[i:i+4], round_keys) for i in range(0, len(data), 4)).hex()

def Simon32_64_hex_decode(text: str, key: str = "secret") -> str:
    try:
        data = bytes.fromhex(text.strip())
    except Exception as e:
        return f"Err:{e}"
    if len(data) % 4:
        return "Err:ciphertext length must be a multiple of 4 bytes"
    round_keys = _simon32_key_schedule(key)
    plain = b"".join(_simon32_decrypt_block(data[i:i+4], round_keys) for i in range(0, len(data), 4))
    return _decode_length_prefixed(plain)

# =============================================================================
# ADFGX / ADFGVX
# =============================================================================

def _columnar_route(s: str, key: str) -> str: return Columnar_encode(s, key)
def _columnar_unroute(s: str, key: str) -> str: return Columnar_decode(s, key)

def ADFGX_encode(text: str, square_key: str = "KEYWORD", route_key: str = "CIPHER") -> str:
    labels = "ADFGX"
    sq, pos, rev = _key_square_5(square_key)
    s = []
    for ch in to_upper(text):
        if ch == 'J': ch = 'I'
        if ch in pos:
            r, c = pos[ch]; s.append(labels[r]); s.append(labels[c])
        elif ch.isdigit():
            word = {"0":"ZERO","1":"ONE","2":"TWO","3":"THREE","4":"FOUR","5":"FIVE",
                    "6":"SIX","7":"SEVEN","8":"EIGHT","9":"NINE"}[ch]
            for w in word:
                r, c = pos[w]; s.append(labels[r]); s.append(labels[c])
    frac = "".join(s)
    return _columnar_route(frac, route_key)

def ADFGX_decode(text: str, square_key: str = "KEYWORD", route_key: str = "CIPHER") -> str:
    labels = "ADFGX"
    sq, pos, rev = _key_square_5(square_key)
    frac = _columnar_unroute(text, route_key)
    out = []
    for i in range(0, len(frac), 2):
        r = labels.index(frac[i]); c = labels.index(frac[i+1])
        out.append(rev[(r,c)])
    return "".join(out).lower()

def ADFGVX_encode(text: str, square_key: str = "KEYW0RD", route_key: str = "CIPHER") -> str:
    labels = "ADFGVX"
    sq, pos, rev = _key_square_6(square_key)
    s = []
    for ch in to_upper(text):
        if ch in pos:
            r, c = pos[ch]; s.append(labels[r]); s.append(labels[c])
    frac = "".join(s)
    return _columnar_route(frac, route_key)

def ADFGVX_decode(text: str, square_key: str = "KEYW0RD", route_key: str = "CIPHER") -> str:
    labels = "ADFGVX"
    sq, pos, rev = _key_square_6(square_key)
    frac = _columnar_unroute(text, route_key)
    out = []
    for i in range(0, len(frac), 2):
        r = labels.index(frac[i]); c = labels.index(frac[i+1])
        out.append(rev[(r,c)])
    return "".join(out).lower()

# =============================================================================
# Morse / Pigpen
# =============================================================================

MORSE_TABLE = {
    'A':'.-','B':'-...','C':'-.-.','D':'-..','E':'.','F':'..-.','G':'--.','H':'....',
    'I':'..','J':'.---','K':'-.-','L':'.-..','M':'--','N':'-.','O':'---','P':'.--.',
    'Q':'--.-','R':'.-.','S':'...','T':'-','U':'..-','V':'...-','W':'.--','X':'-..-',
    'Y':'-.--','Z':'--..',
    '0':'-----','1':'.----','2':'..---','3':'...--','4':'....-','5':'.....',
    '6':'-....','7':'--...','8':'---..','9':'----.',
    '.':'.-.-.-',',':'--..--','?':'..--..',"'":'.----.','!':'-.-.--','/':'-..-.',
    '(':'-.--.',')':'-.--.-','&':'.-...',':':'---...',';':'-.-.-.','=':'-...-',
    '+':'.-.-.','-':'-....-','_':'..--.-','"':'.-..-.','$':'...-..-','@':'.--.-.'
}
MORSE_REV = {v:k for k,v in MORSE_TABLE.items()}

def Morse_encode(text: str) -> str:
    out_words = []
    for word in text.split():
        signs = []
        for ch in word:
            cu = ch.upper()
            if cu in MORSE_TABLE:
                signs.append(MORSE_TABLE[cu])
        out_words.append(" ".join(signs))
    return "[MORSE]|" + " / ".join(out_words)

def Morse_decode(text: str) -> str:
    s = text
    if s.startswith("[MORSE]|"): s = s[len("[MORSE]|"):]
    words = s.split(" / ")
    out = []
    for w in words:
        chars = []
        for code in w.strip().split():
            ch = MORSE_REV.get(code, '')
            if ch: chars.append(ch)
        out.append("".join(chars))
    return " ".join(out)

PIGPEN_MAP = {
    'A':'A1','B':'A2','C':'A3','D':'A4','E':'A5','F':'A6',
    'G':'B1','H':'B2','I':'B3','J':'B3', 'K':'B4','L':'B5','M':'B6',
    'N':'C1','O':'C2','P':'C3','Q':'C4','R':'C5','S':'C6',
    'T':'D1','U':'D2','V':'D3','W':'D4','X':'D5','Y':'D6','Z':'E1'
}
PIGPEN_REV = {}
for k,v in PIGPEN_MAP.items():
    if v not in PIGPEN_REV: PIGPEN_REV[v]=k

def Pigpen_encode(text: str) -> str:
    out = []
    for ch in text:
        cu = ch.upper()
        if cu in PIGPEN_MAP:
            out.append(PIGPEN_MAP[cu])
        elif ch.isspace():
            out.append("/")
        else:
            out.append(ch)
    return "[PIG]|" + " ".join(out)

def Pigpen_decode(text: str) -> str:
    s = text
    if s.startswith("[PIG]|"):
        s = s[len("[PIG]|"):]
    tokens = s.replace("/", " / ").split()
    out = []
    for tok in tokens:
        if tok == "/":
            out.append(" ")
        elif tok in PIGPEN_REV:
            out.append(PIGPEN_REV[tok])
        else:
            out.append(tok if len(tok) == 1 else "")
    return "".join(out)

# =============================================================================
# Quagmire I–IV
# =============================================================================

def _mixed_alpha(key: Optional[str]) -> str:
    return rotate_alpha_from_keyword(key) if key else ALPHA

def _quag_encrypt(text: str, runkey: str, plain_alpha: str, cipher_alpha: str) -> str:
    rk = only_alpha(runkey) or "A"
    out = []
    ki = 0
    for ch in text:
        cu = ch.upper()
        if cu in plain_alpha:
            col = plain_alpha.index(cu)
            row = plain_alpha.index(rk[ki % len(rk)])
            row_alpha = cipher_alpha[row:] + cipher_alpha[:row]
            c = row_alpha[col]
            out.append(c if ch.isupper() else c.lower())
            ki += 1
        else:
            out.append(ch)
    return "".join(out)

def _quag_decrypt(text: str, runkey: str, plain_alpha: str, cipher_alpha: str) -> str:
    rk = only_alpha(runkey) or "A"
    out = []
    ki = 0
    for ch in text:
        cu = ch.upper()
        if cu in cipher_alpha:
            row = plain_alpha.index(rk[ki % len(rk)])
            row_alpha = cipher_alpha[row:] + cipher_alpha[:row]
            col = row_alpha.index(cu)
            p = plain_alpha[col]
            out.append(p if ch.isupper() else p.lower())
            ki += 1
        else:
            out.append(ch)
    return "".join(out)

def QuagmireI_encode(text: str, runkey: str = "QUEENLY", cipher_key: str = "CIPHER") -> str:
    return _quag_encrypt(text, runkey, ALPHA, _mixed_alpha(cipher_key))

def QuagmireI_decode(text: str, runkey: str = "QUEENLY", cipher_key: str = "CIPHER") -> str:
    return _quag_decrypt(text, runkey, ALPHA, _mixed_alpha(cipher_key))

def QuagmireII_encode(text: str, runkey: str = "QUEENLY", plain_key: str = "PLAIN") -> str:
    return _quag_encrypt(text, runkey, _mixed_alpha(plain_key), ALPHA)

def QuagmireII_decode(text: str, runkey: str = "QUEENLY", plain_key: str = "PLAIN") -> str:
    return _quag_decrypt(text, runkey, _mixed_alpha(plain_key), ALPHA)

def QuagmireIII_encode(text: str, runkey: str = "QUEENLY", plain_key: str = "PLAIN", cipher_key: str = "CIPHER") -> str:
    return _quag_encrypt(text, runkey, _mixed_alpha(plain_key), _mixed_alpha(cipher_key))

def QuagmireIII_decode(text: str, runkey: str = "QUEENLY", plain_key: str = "PLAIN", cipher_key: str = "CIPHER") -> str:
    return _quag_decrypt(text, runkey, _mixed_alpha(plain_key), _mixed_alpha(cipher_key))

def QuagmireIV_encode(text: str, runkey: str = "QUEENLY", indicator: str = "INDICATOR", plain_key: str = "PLAIN", cipher_key: str = "CIPHER") -> str:
    pa = _mixed_alpha(plain_key)
    shift = pa.index(only_alpha(indicator)[:1] or 'A')
    rk = only_alpha(runkey)
    rk = rk[shift:] + rk[:shift]
    return _quag_encrypt(text, rk, pa, _mixed_alpha(cipher_key))

def QuagmireIV_decode(text: str, runkey: str = "QUEENLY", indicator: str = "INDICATOR", plain_key: str = "PLAIN", cipher_key: str = "CIPHER") -> str:
    pa = _mixed_alpha(plain_key)
    shift = pa.index(only_alpha(indicator)[:1] or 'A')
    rk = only_alpha(runkey)
    rk = rk[shift:] + rk[:shift]
    return _quag_decrypt(text, rk, pa, _mixed_alpha(cipher_key))

# =============================================================================
# Baconian / Grandpré / Nihilist / Homophonic / Fractionated Morse / Emoji /
# Whitespace / SCB / Rail Fence / XOR(hex) / Base3 / Base9 / Pig Latin / Semaphore
# =============================================================================

# Base3 / Base9
def Base3_encode(text: str) -> str:
    data = text.encode("utf-8")
    n = int.from_bytes(data, "big")
    if n == 0: return "0"
    out = []
    while n > 0:
        n, r = divmod(n, 3)
        out.append("012"[r])
    return "".join(reversed(out))

def Base3_decode(text: str) -> str:
    s = text.strip(); n = 0
    for ch in s:
        if ch not in "012": return "Err:invalid ternary digit"
        n = n*3 + int(ch)
    blen = (n.bit_length() + 7)//8
    return n.to_bytes(blen, "big").decode("utf-8", errors="replace")

def Base9_encode(text: str) -> str:
    data = text.encode("utf-8")
    n = int.from_bytes(data, "big")
    if n == 0: return "0"
    out = []
    while n > 0:
        n, r = divmod(n, 9)
        out.append("012345678"[r])
    return "".join(reversed(out))

def Base9_decode(text: str) -> str:
    s = text.strip(); n = 0
    for ch in s:
        if ch not in "012345678": return "Err:invalid base9 digit"
        n = n*9 + int(ch)
    blen = (n.bit_length() + 7)//8
    return n.to_bytes(blen, "big").decode("utf-8", errors="replace")

# Baconian (I/J combined)
BACON_ALPHA = "ABCDEFGHIKLMNOPQRSTUVWXYZ"
def _bacon_map():
    codes = {}
    for i, ch in enumerate(BACON_ALPHA):
        bits = format(i, "05b")
        code = "".join('A' if b == '0' else 'B' for b in bits)
        codes[ch] = code
    return codes
BACON_CODES = _bacon_map()
BACON_REV = {v:k for k,v in BACON_CODES.items()}

def Baconian_encode(text: str) -> str:
    out = []
    for ch in to_upper(text):
        if ch == 'J': ch = 'I'
        if ch in BACON_CODES:
            out.append(BACON_CODES[ch])
        elif ch.isspace():
            out.append("/")
    return " ".join(out)

def Baconian_decode(text: str) -> str:
    tokens = text.replace("/", " / ").split()
    out = []
    for t in tokens:
        if t == "/": out.append(" "); continue
        if len(t) == 5 and set(t) <= {'A','B'}: out.append(BACON_REV.get(t,''))
    return "".join(out).lower()

# Grandpré
def Grandpre_encode(text: str, key: str = "GRANDPRE") -> str:
    _, pos, _ = _key_square_5(key)
    out = []
    for ch in to_upper(text):
        if ch == 'J': ch = 'I'
        if ch in pos:
            r,c = pos[ch]; out.append(f"{r+1}{c+1}")
        elif ch.isspace():
            out.append("/")
    return " ".join(out)

def Grandpre_decode(text: str, key: str = "GRANDPRE") -> str:
    _, _, rev = _key_square_5(key)
    tokens = text.replace("/", " / ").split()
    out = []
    for t in tokens:
        if t == "/": out.append(" "); continue
        if len(t) == 2 and t.isdigit():
            r = int(t[0])-1; c = int(t[1])-1
            out.append(rev.get((r,c), ''))
    return "".join(out).lower()

# Nihilist (classic)
def Nihilist_encode(text: str, alpha_key: str = "CIPHER", num_key: str = "KEY") -> str:
    _, pos, _ = _key_square_5(alpha_key)
    def numify(s: str) -> List[int]:
        nums = []
        for ch in only_alpha(s):
            r,c = pos['I' if ch=='J' else ch]
            nums.append((r+1)*10 + (c+1))
        return nums
    P = numify(text)
    K = numify(num_key) or [11]
    out = []
    for i, p in enumerate(P):
        out.append(str(p + K[i % len(K)]))
    return " ".join(out)

def Nihilist_decode(text: str, alpha_key: str = "CIPHER", num_key: str = "KEY") -> str:
    _, pos, rev = _key_square_5(alpha_key)
    def numify(s: str) -> List[int]:
        nums = []
        for ch in only_alpha(s):
            r,c = pos['I' if ch=='J' else ch]
            nums.append((r+1)*10 + (c+1))
        return nums
    K = numify(num_key) or [11]
    nums = [int(x) for x in text.replace(",", " ").split()]
    raw = [n - K[i % len(K)] for i, n in enumerate(nums)]
    out = []
    for val in raw:
        r = val // 10 - 1; c = val % 10 - 1
        out.append(rev.get((r,c), ''))
    return "".join(out).lower()

# Homophonic (seeded)
def _homophonic_build(seed: str = "SEED") -> Tuple[Dict[str,List[int]], Dict[int,str]]:
    rnd = random.Random(seed)
    pool = list(range(11, 200))
    rnd.shuffle(pool)
    slots_per = 3
    mapping: Dict[str, List[int]] = {}
    idx = 0
    for ch in ALPHA:
        mapping[ch] = pool[idx:idx+slots_per]; idx += slots_per
    rev = {num: ch for ch, nums in mapping.items() for num in nums}
    return mapping, rev

def HOMO_encode(text: str, seed: str = "SEED") -> str:
    mapping, _ = _homophonic_build(seed)
    rnd = random.Random(seed + "|enc")
    out_tokens = []
    for ch in to_upper(text):
        if ch in mapping:
            out_tokens.append(str(rnd.choice(mapping[ch])))
        elif ch.isspace():
            out_tokens.append("/")
    meta = {"seed": str(seed)}
    return "[HOMO]" + json.dumps(meta) + "|" + " ".join(out_tokens)

def HOMO_decode(text: str) -> str:
    if not text.startswith("[HOMO]"): return "Err:bad format"
    try:
        meta_end = text.index("|", len("[HOMO]"))
        meta_json = text[len("[HOMO]"):meta_end]
        meta = json.loads(meta_json)
        seed = str(meta.get("seed", "SEED"))
        _, rev = _homophonic_build(seed)
        body = text[meta_end+1:]
        out = []
        for tok in body.replace("/", " / ").split():
            if tok == "/": out.append(" "); continue
            try:
                n = int(tok); out.append(rev.get(n, ""))
            except: pass
        return "".join(out).lower()
    except Exception as e:
        return f"Err:{e}"

# Fractionated Morse (robust)
FM_TRIS = ['...','..-','..x','.-.','.--','.-x','.x.','.x-','.xx',
           '-..','-.-','-.x','--.','---','--x','-x.','-x-','-xx',
           'x..','x.-','x.x','x-.','x--','x-x','xx.','xx-','xxx']

def _fm_alpha(key: str) -> str:
    a = rotate_alpha_from_keyword(key)
    return a + "*"

def FM_encode(text: str, key: str = "KEYABCDFGHIJLMNOPQRSTUVWXZ") -> str:
    morse_words = []
    for word in text.split():
        codes = []
        for ch in word:
            cu = ch.upper()
            if cu in MORSE_TABLE:
                codes.append(MORSE_TABLE[cu])
        morse_words.append("x".join(codes))
    frac = "xx".join(morse_words)
    if len(frac) % 3 != 0:
        frac += "x" * (3 - (len(frac) % 3))
    A27 = _fm_alpha(key)
    out = []
    for i in range(0, len(frac), 3):
        tri = frac[i:i+3]
        idx = FM_TRIS.index(tri)
        out.append(A27[idx])
    meta = {"alpha": rotate_alpha_from_keyword(key)}
    return "[FM]" + json.dumps(meta) + "|" + "".join(out)

def FM_decode(text: str, key: str = None) -> str:
    if text.startswith("[FM]"):
        meta_end = text.index("|", len("[FM]"))
        meta = json.loads(text[len("[FM]"):meta_end])
        alpha26 = meta.get("alpha", ALPHA)
        A27 = alpha26 + "*"
        body = text[meta_end+1:]
    else:
        A27 = _fm_alpha(key or "KEY")
        body = text
    out_tris = []
    for ch in body:
        try:
            idx = A27.index(ch)
        except ValueError:
            continue
        out_tris.append(FM_TRIS[idx])
    frac = "".join(out_tris).rstrip('x')
    words = frac.split("xx") if "xx" in frac else [frac]
    out_words = []
    for w in words:
        letters = w.split("x") if w else []
        chars = []
        for sig in letters:
            ch = MORSE_REV.get(sig, '')
            if ch: chars.append(ch)
        out_words.append("".join(chars))
    return " ".join(out_words)

# Emoji (seeded)
EMOJI_POOL = [
    0x1F600,0x1F601,0x1F602,0x1F603,0x1F604,0x1F605,0x1F606,0x1F607,0x1F608,
    0x1F609,0x1F60A,0x1F60B,0x1F60C,0x1F60D,0x1F60E,0x1F60F,0x1F610,0x1F611,
    0x1F612,0x1F613,0x1F614,0x1F615,0x1F616,0x1F617,0x1F618,0x1F619,0x1F61A,
    0x1F61B,0x1F61C,0x1F61D,0x1F61E,0x1F61F,0x1F620,0x1F621,0x1F622,0x1F923,
    0x1F642,0x1F643,0x1F970,0x1F971,0x1F972
]
def _emoji_build(seed: str = "EMOJI") -> Tuple[Dict[str, int], Dict[int, str], List[int]]:
    rnd = random.Random(seed)
    pool = EMOJI_POOL[:]; rnd.shuffle(pool)
    pool = pool[:27]
    mapping = {}
    for i, ch in enumerate(ALPHA + " "):
        mapping[ch] = pool[i]
    rev = {cp: ch for ch, cp in mapping.items()}
    return mapping, rev, pool

def Emoji_encode(text: str, seed: str = "EMOJI") -> str:
    m, _, pool = _emoji_build(seed)
    out = []
    for ch in to_upper(text):
        if ch in m:
            out.append(chr(m[ch]))
        elif ch.isspace():
            out.append(chr(m[" "]))
        else:
            out.append(ch)
    meta = {"map": pool}
    return "[EMOJI]" + json.dumps(meta) + "|" + "".join(out)

def Emoji_decode(text: str) -> str:
    if not text.startswith("[EMOJI]"): return "Err:bad format"
    meta_end = text.index("|", len("[EMOJI]"))
    meta = json.loads(text[len("[EMOJI]"):meta_end])
    pool: List[int] = meta.get("map", [])
    mapping = {}
    for i, ch in enumerate(ALPHA + " "):
        if i < len(pool):
            mapping[pool[i]] = ch
    body = text[meta_end+1:]
    out = []
    for ch in body:
        cp = ord(ch)
        out.append(mapping.get(cp, "" if not ch.isspace() else " "))
    return "".join(out).lower()

# Whitespace
def WS_encode(text: str, n: int | str = None) -> str:
    data = text.encode("utf-8")
    lines = []
    for b in data:
        bits = format(b, "08b")
        line = "".join('\t' if bit == '1' else ' ' for bit in bits)
        lines.append(line)
    meta = {"n": len(data)}
    return "[WS]" + json.dumps(meta) + "|\n" + "\n".join(lines)

def WS_decode(text: str, n: int | str = None) -> str:
    if not text.startswith("[WS]"): return "Err:bad format"
    meta_end = text.index("|", len("[WS]"))
    body = text[meta_end+1:]
    bytes_out = []
    for line in body.splitlines():
        bits = "".join('1' if ch == '\t' else ('0' if ch == ' ' else '') for ch in line)
        if len(bits) == 8:
            bytes_out.append(int(bits, 2))
    return bytes(bytes_out).decode("utf-8", errors="replace")

# SCB
def _scb_tables(keyword: str = "ETAOINSHRDLCUMWFGYPBVKJXQZ",
                rowdigits: Tuple[int,int] = (3,7)) -> Tuple[Dict[str,str], Dict[str,str]]:
    header = "0123456789"
    rd1, rd2 = rowdigits
    first_cols = [d for d in header if d not in (str(rd1), str(rd2))]
    kw = rotate_alpha_from_keyword(keyword)
    firstrow_letters = list(kw[:len(first_cols)])
    remaining = [ch for ch in kw[len(first_cols):]]
    second = remaining[:10]
    third = remaining[10:20]
    enc: Dict[str,str] = {}; dec: Dict[str,str] = {}
    for d, ch in zip(first_cols, firstrow_letters):
        enc[ch] = d; dec[d] = ch
    for i, ch in enumerate(second):
        code = f"{rd1}{i}"; enc[ch] = code; dec[code] = ch
    for i, ch in enumerate(third):
        code = f"{rd2}{i}"; enc[ch] = code; dec[code] = ch
    return enc, dec

def SCB_encode(text: str, keyword: str = "ETAOINSHRDLCUMWFGYPBVKJXQZ", rowdigits: Tuple[int,int]=(3,7)) -> str:
    enc, _ = _scb_tables(keyword, rowdigits)
    out_tokens = []
    for ch in to_upper(text):
        if ch in enc:
            out_tokens.append(enc[ch])
        elif ch.isspace():
            out_tokens.append("/")
    return " ".join(out_tokens)

def SCB_decode(text: str, keyword: str = "ETAOINSHRDLCUMWFGYPBVKJXQZ", rowdigits: Tuple[int,int]=(3,7)) -> str:
    _, dec = _scb_tables(keyword, rowdigits)
    tokens = text.replace("/", " / ").split()
    out = []
    for t in tokens:
        if t == "/":
            out.append(" "); continue
        if t in dec: out.append(dec[t])
    return "".join(out).lower()

# Rail Fence
def RailFence_encode(text: str, rails: int | str = 3) -> str:
    if isinstance(rails, str): rails = int(rails)
    s = "".join(ch for ch in text if not ch.isspace())
    fence = [[] for _ in range(rails)]
    r = 0; dr = 1
    for ch in s:
        fence[r].append(ch); r += dr
        if r == 0 or r == rails-1: dr *= -1
    return "".join("".join(row) for row in fence)

def RailFence_decode(text: str, rails: int | str = 3) -> str:
    if isinstance(rails, str): rails = int(rails)
    s = text
    marks = [None]*len(s); r = 0; dr = 1
    for i in range(len(s)):
        marks[i] = r; r += dr
        if r == 0 or r == rails-1: dr *= -1
    counts = [marks.count(r) for r in range(rails)]
    idx = 0; rails_data = []
    for count in counts:
        rails_data.append(list(s[idx:idx+count])); idx += count
    out = []; r_pos = [0]*rails
    for i in range(len(s)):
        rail = marks[i]; out.append(rails_data[rail][r_pos[rail]]); r_pos[rail] += 1
    return "".join(out)

# XOR(hex)
def XOR_hex_encode(text: str, key: str = "key") -> str:
    data = text.encode("utf-8"); k = key.encode("utf-8") or b"\x00"
    out = bytes(data[i] ^ k[i % len(k)] for i in range(len(data)))
    return out.hex()

def XOR_hex_decode(text: str, key: str = "key") -> str:
    try:
        data = bytes.fromhex(text)
    except Exception as e:
        return f"Err:{e}"
    k = key.encode("utf-8") or b"\x00"
    out = bytes(data[i] ^ k[i % len(k)] for i in range(len(data)))
    return out.decode("utf-8", errors="replace")

# Pig Latin
VOWELS = set("AEIOU")
def PigLatin_encode(text: str) -> str:
    def enc_word(w: str) -> str:
        if not w: return w
        u = w.upper()
        if u[0] in VOWELS: return u + "-yay"
        i = 0
        while i < len(u) and u[i] not in VOWELS: i += 1
        return u[i:] + "-" + u[:i].lower() + "ay"
    out = []
    for tok in text.split(" "):
        out.append(enc_word(tok) if tok.strip() else "")
    return "[PL]|" + " ".join(out)

def PigLatin_decode(text: str) -> str:
    s = text
    if s.startswith("[PL]|"): s = s[len("[PL]|"):]
    def dec_word(w: str) -> str:
        if not w: return w
        if w.endswith("-yay"): return w[:-4]
        if w.endswith("ay") and "-" in w:
            base = w[:-2]; i = base.rfind("-")
            if i != -1:
                suffix = base[i+1:]; root = base[:i]
                return suffix.upper() + root
        return w
    return " ".join(dec_word(tok) for tok in s.split(" "))

# Semaphore (tokenized)
SEMAPHORE_MAP = {
    'A':'NW','B':'N','C':'NE','D':'W','E':'C','F':'E','G':'SW','H':'S','I':'SE','J':'W2',
    'K':'NE2','L':'E2','M':'S2','N':'SW2','O':'NW2','P':'N2','Q':'C2','R':'SE2','S':'W3','T':'E3',
    'U':'N3','V':'S3','W':'NW3','X':'NE3','Y':'SW3','Z':'SE3'
}
SEMAPHORE_REV = {v:k for k,v in SEMAPHORE_MAP.items()}

def Semaphore_encode(text: str) -> str:
    out = []
    for ch in to_upper(text):
        if ch in SEMAPHORE_MAP:
            out.append(SEMAPHORE_MAP[ch])
        elif ch.isspace():
            out.append("/")
    return "[SEM]|" + " ".join(out)

def Semaphore_decode(text: str) -> str:
    s = text
    if s.startswith("[SEM]|"):
        s = s[len("[SEM]|"):]
    out = []
    for tok in s.replace("/", " / ").split():
        if tok == "/": out.append(" ")
        else: out.append(SEMAPHORE_REV.get(tok, ""))
    return "".join(out).lower()

# =============================================================================
# Smart English scoring + SmartGuess + BruteForce (CORE)
# =============================================================================

# simple English letter frequency (percentages)
_EN_FREQ = {
    'E':12.70,'T':9.06,'A':8.17,'O':7.51,'I':6.97,'N':6.75,'S':6.33,'H':6.09,'R':5.99,'D':4.25,
    'L':4.03,'C':2.78,'U':2.76,'M':2.41,'W':2.36,'F':2.23,'G':2.02,'Y':1.97,'P':1.93,'B':1.49,
    'V':0.98,'K':0.77,'J':0.15,'X':0.15,'Q':0.10,'Z':0.07
}

def _chi_squared_english(s: str) -> float:
    t = only_alpha(s)
    n = len(t)
    if n == 0: return float('inf')
    counts = {ch:0 for ch in ALPHA}
    for ch in t: counts[ch] += 1
    chi = 0.0
    for ch in ALPHA:
        expected = _EN_FREQ[ch] * n / 100.0
        diff = counts[ch] - expected
        chi += (diff*diff) / (expected if expected > 0 else 1e-9)
    # small penalty if few spaces in an otherwise long string
    space_penalty = 0.0
    # (Leave mild, spaces may have been stripped by some ciphers)
    return chi + space_penalty

def english_score(s: str) -> float:
    # combine chi-squared with a penalty for high non-printable ratio
    if not s: return float('inf')
    chi = _chi_squared_english(s)
    bad = sum(1 for ch in s if ord(ch) < 9 or (13 < ord(ch) < 32))
    return chi + bad*5.0

def is_printable_ratio_ok(s: str, thresh: float = 0.85) -> bool:
    if not s: return False
    vis = sum(1 for ch in s if (32 <= ord(ch) <= 126) or ch in "\n\r\t")
    return (vis / len(s)) >= thresh

def looks_hex(s: str) -> bool:
    s2 = s.strip().replace(" ", "")
    if len(s2) < 2 or len(s2)%2==1: return False
    return all(ch in "0123456789abcdefABCDEF" for ch in s2)

def looks_base64(s: str) -> bool:
    s2 = s.strip().replace("\n", "").replace(" ", "")
    if len(s2) % 4 != 0: return False
    return all(ch in (string.ascii_letters + string.digits + "+/=") for ch in s2)

def looks_dna(s: str) -> bool:
    s2 = s.strip().replace(" ", "")
    if not s2: return False
    return all(ch in "ACGTacgt" for ch in s2)

def looks_polybius_grandpre(s: str) -> bool:
    toks = s.replace("/", " / ").split()
    if not toks: return False
    return all((t==" / " or t=="/" or (t.isdigit() and 1 <= len(t) <= 2)) for t in toks)

def looks_bacon(s: str) -> bool:
    toks = s.replace("/", " / ").split()
    if not toks: return False
    return all((t==" / " or t=="/" or (len(t)==5 and set(t)<=set("AB"))) for t in toks)

def looks_morse(s: str) -> bool:
    return set(ch for ch in s if not ch.isspace()) <= set(".-//")

def looks_adfgx(s: str) -> bool:
    letters = set(ch for ch in s if ch.isalpha())
    return letters <= set("ADFGXadfgx")

def looks_adfgvx(s: str) -> bool:
    letters = set(ch for ch in s if ch.isalpha())
    return letters <= set("ADFGVXadfgvx")

def SmartGuess(text: str) -> List[Tuple[str, str, float]]:
    """
    Return ranked list of (label, plaintext, score) candidates.
    Detect tags first, then heuristics, else brute a few families.
    Lower score = better.
    """
    t = text.strip()
    candidates: List[Tuple[str,str,float]] = []

    # 1) Tagged formats — decode straight
    try:
        if t.startswith("[HOMO]"):
            pt = HOMO_decode(t); candidates.append(("Homophonic (tag)", pt, english_score(pt)))
        if t.startswith("[EMOJI]"):
            pt = Emoji_decode(t); candidates.append(("Emoji (tag)", pt, english_score(pt)))
        if t.startswith("[WS]"):
            pt = WS_decode(t); candidates.append(("Whitespace (tag)", pt, english_score(pt)))
        if t.startswith("[FM]"):
            pt = FM_decode(t); candidates.append(("Fractionated Morse (tag)", pt, english_score(pt)))
        if t.startswith("[MORSE]|"):
            pt = Morse_decode(t); candidates.append(("Morse (tag)", pt, english_score(pt)))
        if t.startswith("[PIG]|"):
            pt = Pigpen_decode(t); candidates.append(("Pigpen (tag)", pt, english_score(pt)))
        if t.startswith("[PL]|"):
            pt = PigLatin_decode(t); candidates.append(("Pig Latin (tag)", pt, english_score(pt)))
        if t.startswith("[SEM]|"):
            pt = Semaphore_decode(t); candidates.append(("Semaphore (tag)", pt, english_score(pt)))
        if t.startswith("[LEET]|"):
            pt = LEET_decode(t); candidates.append(("Leet (tag)", pt, english_score(pt)))
    except Exception:
        pass

    # 2) Pattern-based decodes
    try:
        if looks_hex(t):
            pt = Hex_decode(t); candidates.append(("Hex", pt, english_score(pt)))
            # XOR-hex single byte brute
            data = bytes.fromhex(t.strip().replace(" ",""))
            best = None
            for k in range(256):
                out = bytes(b ^ k for b in data)
                try:
                    s = out.decode("utf-8", errors="replace")
                except: 
                    continue
                sc = english_score(s)
                if best is None or sc < best[2]:
                    best = (f"XOR-hex single-byte k={k}", s, sc)
            if best: candidates.append(best)
        if looks_base64(t):
            pt = Base64_decode(t); candidates.append(("Base64", pt, english_score(pt)))
        if looks_dna(t):
            pt = DNA_decode(t); candidates.append(("DNA", pt, english_score(pt)))
        if looks_bacon(t):
            pt = Baconian_decode(t); candidates.append(("Baconian", pt, english_score(pt)))
        if looks_polybius_grandpre(t):
            # Try both with default keys
            pt1 = Polybius_decode(t, "KEYWORD"); candidates.append(("Polybius (guess)", pt1, english_score(pt1)))
            pt2 = Grandpre_decode(t, "GRANDPRE"); candidates.append(("Grandpré (guess)", pt2, english_score(pt2)))
        if looks_morse(t) or t.startswith("[MORSE]|"):
            pt = Morse_decode(t); candidates.append(("Morse", pt, english_score(pt)))
        if looks_adfgx(t):
            pt = ADFGX_decode(t, "KEYWORD", "CIPHER"); candidates.append(("ADFGX default-keys", pt, english_score(pt)))
        if looks_adfgvx(t):
            pt = ADFGVX_decode(t, "KEYW0RD", "CIPHER"); candidates.append(("ADFGVX default-keys", pt, english_score(pt)))
    except Exception:
        pass

    # 3) Lightweight brute force: Caesar (all), Affine (coprimes), RailFence(2..8)
    #    + short Vigenère (keys length 1..2 from ETAOINSHRDLU), ROT13/47, Atbash
    sU = to_upper(t)
    # Caesar/ROT/Atbash
    for sh in range(26):
        pt = Caesar_decode(sU, sh); candidates.append((f"Caesar -{sh}", pt, english_score(pt)))
    candidates.append(("ROT13", ROT13_decode(t), english_score(ROT13_decode(t))))
    candidates.append(("ROT47", ROT47_decode(t), english_score(ROT47_decode(t))))
    candidates.append(("Atbash", Atbash_decode(t), english_score(Atbash_decode(t))))

    # Affine brute
    coprimes = [a for a in range(1,26) if math.gcd(a,26)==1]
    for a in coprimes:
        for b in range(26):
            try:
                pt = Affine_decode(sU, a, b, 26)
                candidates.append((f"Affine a={a} b={b}", pt, english_score(pt)))
            except Exception:
                pass

    # Rail Fence
    for rails in range(2, 9):
        try:
            pt = RailFence_decode(t.replace(" ",""), rails)
            candidates.append((f"RailFence rails={rails}", pt, english_score(pt)))
        except Exception:
            pass

    # Short-key Vigenère brute over ETAOINSHRDLU (length 1..2)
    pool = "ETAOINSHRDLU"
    keys = set()
    for a in pool:
        keys.add(a)
        for b in pool:
            keys.add(a+b)
    for k in keys:
        pt = Vigenere_decode(sU, k)
        candidates.append((f"Vigenere key={k}", pt, english_score(pt)))

    # Rank and return top
    # Remove exact duplicate plaintexts with worse scores
    best_map: Dict[str, Tuple[str,str,float]] = {}
    for label, pt, sc in candidates:
        if not pt: continue
        key = pt
        if key not in best_map or sc < best_map[key][2]:
            best_map[key] = (label, pt, sc)
    ranked = sorted(best_map.values(), key=lambda x: x[2])
    return ranked[:30]  # top 30 for inspection

def BruteForce(text: str, families: Optional[List[str]] = None) -> List[Tuple[str,str,float]]:
    """
    Explicit brute force across requested families (subset of):
      ["caesar","affine","railfence","vigenere-short","xor-hex"]
    Returns ranked list (label, plaintext, score).
    """
    fam = set((f or "").lower() for f in (families or ["caesar","affine","railfence","vigenere-short","xor-hex"]))
    t = text
    cands: List[Tuple[str,str,float]] = []

    if "caesar" in fam:
        sU = to_upper(t)
        for sh in range(26):
            pt = Caesar_decode(sU, sh); cands.append((f"Caesar -{sh}", pt, english_score(pt)))

    if "affine" in fam:
        sU = to_upper(t)
        for a in [a for a in range(1,26) if math.gcd(a,26)==1]:
            for b in range(26):
                try:
                    pt = Affine_decode(sU, a, b, 26)
                    cands.append((f"Affine a={a} b={b}", pt, english_score(pt)))
                except Exception:
                    pass

    if "railfence" in fam:
        s = t.replace(" ","")
        for rails in range(2, 11):
            try:
                pt = RailFence_decode(s, rails)
                cands.append((f"RailFence rails={rails}", pt, english_score(pt)))
            except Exception:
                pass

    if "vigenere-short" in fam:
        sU = to_upper(t)
        pool = "ETAOINSHRDLU"
        keys = set()
        for a in pool:
            keys.add(a)
            for b in pool:
                keys.add(a+b)
        for k in keys:
            pt = Vigenere_decode(sU, k)
            cands.append((f"Vigenere key={k}", pt, english_score(pt)))

    if "xor-hex" in fam and looks_hex(t):
        try:
            data = bytes.fromhex(t.strip().replace(" ",""))
            for k in range(256):
                out = bytes(b ^ k for b in data)
                s = out.decode("utf-8", errors="replace")
                sc = english_score(s)
                cands.append((f"XOR-hex single-byte k={k}", s, sc))
        except Exception:
            pass

    # rank, dedupe plaintext
    best_map: Dict[str, Tuple[str,str,float]] = {}
    for label, pt, sc in cands:
        if pt not in best_map or sc < best_map[pt][2]:
            best_map[pt] = (label, pt, sc)
    ranked = sorted(best_map.values(), key=lambda x: x[2])
    return ranked[:50]

# =============================================================================
# Patches / robustness tweaks (safe on odd-length inputs & edge cases)
# =============================================================================

def _pairwise(s: str) -> List[Tuple[str,str]]:
    L = len(s)
    # If odd, ignore last dangling char instead of raising
    rng = range(0, L - (L % 2), 2)
    return [(s[i], s[i+1]) for i in rng]

def ADFGX_decode(text: str, square_key: str = "KEYWORD", route_key: str = "CIPHER") -> str:
    labels = "ADFGX"
    sq, pos, rev = _key_square_5(square_key)
    frac = _columnar_unroute(text, route_key)
    out = []
    for a,b in _pairwise(frac):
        if a not in labels or b not in labels: continue
        r = labels.index(a); c = labels.index(b)
        out.append(rev.get((r,c), ''))
    return "".join(out).lower()

def ADFGVX_decode(text: str, square_key: str = "KEYW0RD", route_key: str = "CIPHER") -> str:
    labels = "ADFGVX"
    sq, pos, rev = _key_square_6(square_key)
    frac = _columnar_unroute(text, route_key)
    out = []
    for a,b in _pairwise(frac):
        if a not in labels or b not in labels: continue
        r = labels.index(a); c = labels.index(b)
        out.append(rev.get((r,c), ''))
    return "".join(out).lower()

def FM_decode(text: str, key: str = None) -> str:
    # Accept both tagged & raw bodies, tolerate unknown chars, ignore padding/dangling
    if text.startswith("[FM]"):
        meta_end = text.index("|", len("[FM]"))
        meta = json.loads(text[len("[FM]"):meta_end])
        alpha26 = meta.get("alpha", ALPHA)
        A27 = alpha26 + "*"
        body = text[meta_end+1:]
    else:
        A27 = _fm_alpha(key or "KEY")
        body = text
    out_tris = []
    for ch in body:
        try:
            idx = A27.index(ch)
        except ValueError:
            # ignore extraneous chars
            continue
        out_tris.append(FM_TRIS[idx])
    frac = "".join(out_tris).rstrip('x')
    # Split into words by 'xx' separators (if any)
    words = frac.split("xx") if "xx" in frac else [frac]
    out_words = []
    for w in words:
        # Split letters by single x (if any)
        letters = w.split("x") if w else []
        chars = []
        for sig in letters:
            ch = MORSE_REV.get(sig, '')
            if ch: chars.append(ch)
        out_words.append("".join(chars))
    return " ".join(out_words)

# =============================================================================
# Cipher registry (name -> encoder/decoder + param schema)
# =============================================================================

from dataclasses import dataclass, field
import os
from pathlib import Path
import argparse
import sys
import time

@dataclass
class Param:
    name: str
    label: str
    default: str
    tip: str = ""

@dataclass
class CipherEntry:
    name: str
    enc_fn: callable
    dec_fn: callable
    params: List[Param] = field(default_factory=list)

def get_registry() -> List[CipherEntry]:
    P = Param  # alias
    reg: List[CipherEntry] = [
        # Shifts / subs
        CipherEntry("Caesar", Caesar_encode, Caesar_decode, [P("shift","Shift","3","Integer")]),
        CipherEntry("ROT13", ROT13_encode, ROT13_decode, []),
        CipherEntry("ROT5", ROT5_encode, ROT5_decode, []),
        CipherEntry("ROT18", ROT18_encode, ROT18_decode, []),
        CipherEntry("ROT47", ROT47_encode, ROT47_decode, []),
        CipherEntry("Atbash", Atbash_encode, Atbash_decode, []),
        CipherEntry("Affine", Affine_encode, Affine_decode, [P("a","a","5"), P("b","b","8"), P("m","mod","26")]),
        CipherEntry("Keyword Shift", KeywordShift_encode, KeywordShift_decode, [P("keyword","Keyword","CIPHER")]),
        CipherEntry("Keyword Substitution", KeywordSubstitute_encode, KeywordSubstitute_decode, [P("keyword","Keyword","CIPHER")]),

        # Vigenère family
        CipherEntry("Vigenere", Vigenere_encode, Vigenere_decode, [P("key","Key","LEMON")]),
        CipherEntry("Autokey", Autokey_encode, Autokey_decode, [P("key","Key","QUEENLY")]),
        CipherEntry("Beaufort", Beaufort_encode, Beaufort_decode, [P("key","Key","FORT")]),
        CipherEntry("Gronsfeld", Gronsfeld_encode, Gronsfeld_decode, [P("key","Digits","314159")]),
        CipherEntry("Porta (historic)", PortaHistoric_encode, PortaHistoric_decode, [P("key","Key","PORTA")]),
        CipherEntry("Porta (table)", PortaTable_encode, PortaTable_decode, [P("key","Key","PORTA")]),
        CipherEntry("Running Key", RunningKey_encode, RunningKey_decode, [P("key","Key","THENEVERENDINGSTORY")]),
        CipherEntry("OTP (letters)", OTPLetters_encode, OTPLetters_decode, [P("key","Key","XMCKL")]),

        # Fun / novelty
        CipherEntry("Backslang", Backslang_encode, Backslang_decode, []),
        CipherEntry("Rövarspråket", Rovarspraket_encode, Rovarspraket_decode, []),
        CipherEntry("Tutnese", Tutnese_encode, Tutnese_decode, []),
        CipherEntry("Leet Speak", LEET_encode, LEET_decode, []),
        CipherEntry("Keyboard Substitution", KeyboardSub_encode, KeyboardSub_decode, []),
        CipherEntry("Keyboard Reversed", KeyboardReversed_encode, KeyboardReversed_decode, []),
        CipherEntry("A1Z26", A1Z26_encode, A1Z26_decode, []),
        CipherEntry("NATO Phonetic", NATO_encode, NATO_decode, []),
        CipherEntry("Braille Unicode", BrailleUnicode_encode, BrailleUnicode_decode, []),

        # Encodings
        CipherEntry("Binary", Binary_encode, Binary_decode, []),
        CipherEntry("Octal", Octal_encode, Octal_decode, []),
        CipherEntry("Hex", Hex_encode, Hex_decode, []),
        CipherEntry("Base32", Base32_encode, Base32_decode, []),
        CipherEntry("Base32 Crockford", Base32Crockford_encode, Base32Crockford_decode, []),
        CipherEntry("Base36", Base36_encode, Base36_decode, []),
        CipherEntry("Base45", Base45_encode, Base45_decode, []),
        CipherEntry("Base58", Base58_encode, Base58_decode, []),
        CipherEntry("Base64", Base64_encode, Base64_decode, []),
        CipherEntry("Ascii85 (a85)", A85_encode, A85_decode, []),
        CipherEntry("Base85 (b85)", B85_encode, B85_decode, []),
        CipherEntry("Base3 (ternary)", Base3_encode, Base3_decode, []),
        CipherEntry("Base9", Base9_encode, Base9_decode, []),
        CipherEntry("URL", URL_encode, URL_decode, []),
        CipherEntry("HTML Entities", HTMLEntities_encode, HTMLEntities_decode, []),
        CipherEntry("Quoted-Printable", QuotedPrintable_encode, QuotedPrintable_decode, []),
        CipherEntry("Unicode \\u Escapes", UEscapes_encode, UEscapes_decode, []),
        CipherEntry("ASCII Shift (hex)", AsciiShiftHex_encode, AsciiShiftHex_decode, [P("shift","Shift","1")]),
        CipherEntry("DNA Encoding", DNA_encode, DNA_decode, []),

        # Polygraphic / transposition
        CipherEntry("Polybius", Polybius_encode, Polybius_decode, [P("key","Key","KEYWORD")]),
        CipherEntry("Playfair", Playfair_encode, Playfair_decode, [P("key","Key","KEYWORD")]),
        CipherEntry("Four-Square", FourSquare_encode, FourSquare_decode, [P("key1","Key 1","EXAMPLE"), P("key2","Key 2","KEYWORD")]),
        CipherEntry("Two-Square", TwoSquare_encode, TwoSquare_decode, [P("key1","Key L","EXAMPLE"), P("key2","Key R","KEYWORD")]),
        CipherEntry("Columnar", Columnar_encode, Columnar_decode, [P("key","Key","CIPHER")]),
        CipherEntry("Myszkowski", Myszkowski_encode, Myszkowski_decode, [P("key","Key","TOMATO")]),
        CipherEntry("Caesar Box", CaesarBox_encode, CaesarBox_decode, [P("cols","Cols","4")]),
        CipherEntry("Scytale", Scytale_encode, Scytale_decode, [P("diameter","Diameter","5")]),
        CipherEntry("Double Transposition", DoubleTransposition_encode, DoubleTransposition_decode, [P("key1","Key 1","EXAMPLE"), P("key2","Key 2","KEYWORD")]),
        CipherEntry("Route Cipher", Route_encode, Route_decode, [P("rows","Rows","5"), P("cols","Cols","5")]),
        CipherEntry("Bifid", Bifid_encode, Bifid_decode, [P("key","Key","KEYWORD"), P("period","Period","5")]),
        CipherEntry("Trifid", Trifid_encode, Trifid_decode, [P("key","Key","KEYWORD"), P("period","Period","5")]),
        CipherEntry("Hill 2x2", Hill2x2_encode, Hill2x2_decode, [P("key","Matrix key","3,3,2,5")]),

        # ADFGX / ADFGVX
        CipherEntry("ADFGX", ADFGX_encode, ADFGX_decode, [P("square_key","Square Key","KEYWORD"), P("route_key","Route Key","CIPHER")]),
        CipherEntry("ADFGVX", ADFGVX_encode, ADFGVX_decode, [P("square_key","Square Key","KEYW0RD"), P("route_key","Route Key","CIPHER")]),

        # Morse / Pigpen
        CipherEntry("Morse", Morse_encode, Morse_decode, []),
        CipherEntry("Pigpen", Pigpen_encode, Pigpen_decode, []),

        # Quagmire I–IV
        CipherEntry("Quagmire I", QuagmireI_encode, QuagmireI_decode, [P("runkey","Run-key","QUEENLY"), P("cipher_key","Cipher-key","CIPHER")]),
        CipherEntry("Quagmire II", QuagmireII_encode, QuagmireII_decode, [P("runkey","Run-key","QUEENLY"), P("plain_key","Plain-key","PLAIN")]),
        CipherEntry("Quagmire III", QuagmireIII_encode, QuagmireIII_decode, [P("runkey","Run-key","QUEENLY"), P("plain_key","Plain-key","PLAIN"), P("cipher_key","Cipher-key","CIPHER")]),
        CipherEntry("Quagmire IV", QuagmireIV_encode, QuagmireIV_decode, [P("runkey","Run-key","QUEENLY"), P("indicator","Indicator","INDICATOR"), P("plain_key","Plain-key","PLAIN"), P("cipher_key","Cipher-key","CIPHER")]),

        # Numeric / fractionated
        CipherEntry("Baconian", Baconian_encode, Baconian_decode, []),
        CipherEntry("Grandpré", Grandpre_encode, Grandpre_decode, [P("key","Key","GRANDPRE")]),
        CipherEntry("Nihilist", Nihilist_encode, Nihilist_decode, [P("alpha_key","Alpha-key","CIPHER"), P("num_key","Num-key","KEY")]),
        CipherEntry("Homophonic", HOMO_encode, HOMO_decode, [P("seed","Seed","SEED")]),
        CipherEntry("Fractionated Morse", FM_encode, FM_decode, [P("key","Key","KEYABCDFGHIJLMNOPQRSTUVWXZ")]),

        # Modern / recently created
        CipherEntry("RC4 (hex)", RC4_hex_encode, RC4_hex_decode, [P("key","Key","secret")]),
        CipherEntry("Solitaire", Solitaire_encode, Solitaire_decode, [P("key","Key","CRYPTONOMICON")]),
        CipherEntry("ChaCha20 (hex)", ChaCha20_hex_encode, ChaCha20_hex_decode, [P("key","Key","secret"), P("nonce","Nonce","000000000000000000000000"), P("counter","Counter","1")]),
        CipherEntry("ChaCha12 (hex)", ChaCha12_hex_encode, ChaCha12_hex_decode, [P("key","Key","secret"), P("nonce","Nonce","000000000000000000000000"), P("counter","Counter","1")]),
        CipherEntry("ChaCha8 (hex)", ChaCha8_hex_encode, ChaCha8_hex_decode, [P("key","Key","secret"), P("nonce","Nonce","000000000000000000000000"), P("counter","Counter","1")]),
        CipherEntry("Salsa20 (hex)", Salsa20_hex_encode, Salsa20_hex_decode, [P("key","Key","secret"), P("nonce","Nonce","0000000000000000"), P("counter","Counter","0")]),
        CipherEntry("XXTEA (hex)", XXTEA_hex_encode, XXTEA_hex_decode, [P("key","Key","secret")]),
        CipherEntry("Speck32/64 (hex)", Speck32_hex_encode, Speck32_hex_decode, [P("key","Key","secret")]),
        CipherEntry("Simon32/64 (hex)", Simon32_64_hex_encode, Simon32_64_hex_decode, [P("key","Key","secret")]),
        CipherEntry("TEA (hex)", TEA_hex_encode, TEA_hex_decode, [P("key","Key","secret")]),
        CipherEntry("XTEA (hex)", XTEA_hex_encode, XTEA_hex_decode, [P("key","Key","secret")]),
        CipherEntry("RC5-32/12/16 (hex)", RC5_32_hex_encode, RC5_32_hex_decode, [P("key","Key","secret")]),

        # Novel tagged
        CipherEntry("Emoji Substitution", Emoji_encode, Emoji_decode, [P("seed","Seed","EMOJI")]),
        CipherEntry("Whitespace Encoding", WS_encode, WS_decode, []),
        CipherEntry("SCB Encode", SCB_encode, SCB_decode, [P("keyword","Keyword","ETAOINSHRDLCUMWFGYPBVKJXQZ"), P("rowdigits","RowDigits","3,7")]),
        CipherEntry("Rail Fence", RailFence_encode, RailFence_decode, [P("rails","Rails","3")]),
        CipherEntry("XOR (hex)", XOR_hex_encode, XOR_hex_decode, [P("key","Key","key")]),
        CipherEntry("Pig Latin", PigLatin_encode, PigLatin_decode, []),
        CipherEntry("Semaphore", Semaphore_encode, Semaphore_decode, []),
    ]
    return reg

# =============================================================================
# Helpers: call by name with param dict
# =============================================================================

def _parse_rowdigits(v: str) -> tuple[int,int]:
    try:
        a,b = v.split(",")
        return (int(a.strip()), int(b.strip()))
    except:
        return (3,7)

def call_encode(name: str, text: str, params: Dict[str,str]) -> str:
    for ce in get_registry():
        if ce.name == name:
            # Normalize param types for a couple of ciphers
            if name == "Affine":
                return ce.enc_fn(text, int(params.get("a","5")), int(params.get("b","8")), int(params.get("m","26")))
            if name == "ASCII Shift (hex)":
                return ce.enc_fn(text, int(params.get("shift","1")))
            if name == "Columnar":
                return ce.enc_fn(text, params.get("key","CIPHER"))
            if name == "Myszkowski":
                return ce.enc_fn(text, params.get("key","TOMATO"))
            if name == "Caesar Box":
                return ce.enc_fn(text, int(params.get("cols","4")))
            if name == "Scytale":
                return ce.enc_fn(text, int(params.get("diameter","5")))
            if name == "Route Cipher":
                return ce.enc_fn(text, int(params.get("rows","5")), int(params.get("cols","5")))
            if name == "ADFGX":
                return ce.enc_fn(text, params.get("square_key","KEYWORD"), params.get("route_key","CIPHER"))
            if name == "ADFGVX":
                return ce.enc_fn(text, params.get("square_key","KEYW0RD"), params.get("route_key","CIPHER"))
            if name == "SCB Encode":
                return ce.enc_fn(text, params.get("keyword","ETAOINSHRDLCUMWFGYPBVKJXQZ"), _parse_rowdigits(params.get("rowdigits","3,7")))
            if name == "Rail Fence":
                return ce.enc_fn(text, int(params.get("rails","3")))
            # Defaults: pass exactly as strings in declared order
            # Collect kwargs in order:
            ordered = []
            for p in ce.params:
                ordered.append(params.get(p.name, p.default))
            return ce.enc_fn(text, *ordered)
    raise ValueError(f"Unknown cipher: {name}")

def call_decode(name: str, text: str, params: Dict[str,str]) -> str:
    for ce in get_registry():
        if ce.name == name:
            if name == "Affine":
                return ce.dec_fn(text, int(params.get("a","5")), int(params.get("b","8")), int(params.get("m","26")))
            if name == "ASCII Shift (hex)":
                return ce.dec_fn(text, int(params.get("shift","1")))
            if name == "Columnar":
                return ce.dec_fn(text, params.get("key","CIPHER"))
            if name == "Myszkowski":
                return ce.dec_fn(text, params.get("key","TOMATO"))
            if name == "Caesar Box":
                return ce.dec_fn(text, int(params.get("cols","4")))
            if name == "Scytale":
                return ce.dec_fn(text, int(params.get("diameter","5")))
            if name == "Route Cipher":
                return ce.dec_fn(text, int(params.get("rows","5")), int(params.get("cols","5")))
            if name == "ADFGX":
                return ce.dec_fn(text, params.get("square_key","KEYWORD"), params.get("route_key","CIPHER"))
            if name == "ADFGVX":
                return ce.dec_fn(text, params.get("square_key","KEYW0RD"), params.get("route_key","CIPHER"))
            if name == "SCB Encode":
                return ce.dec_fn(text, params.get("keyword","ETAOINSHRDLCUMWFGYPBVKJXQZ"), _parse_rowdigits(params.get("rowdigits","3,7")))
            if name == "Rail Fence":
                return ce.dec_fn(text, int(params.get("rails","3")))
            # Defaults
            ordered = []
            for p in ce.params:
                ordered.append(params.get(p.name, p.default))
            return ce.dec_fn(text, *ordered)
    raise ValueError(f"Unknown cipher: {name}")

# =============================================================================
# CLI
# =============================================================================

def parse_kv_list(kv_list: List[str]) -> Dict[str,str]:
    out = {}
    for kv in kv_list or []:
        if "=" in kv:
            k,v = kv.split("=",1)
            out[k.strip()] = v.strip()
    return out

def cli_main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(prog="encripter", description="All-The-Ciphers — encode/decode/guess/bruteforce")
    sub = parser.add_subparsers(dest="cmd")

    p_list = sub.add_parser("list", help="List ciphers")
    p_enc = sub.add_parser("encode", help="Encode text")
    p_enc.add_argument("cipher")
    p_enc.add_argument("text")
    p_enc.add_argument("-p","--param", action="append", help="key=value", default=[])

    p_dec = sub.add_parser("decode", help="Decode text")
    p_dec.add_argument("cipher")
    p_dec.add_argument("text")
    p_dec.add_argument("-p","--param", action="append", help="key=value", default=[])

    p_guess = sub.add_parser("guess", help="Smart guess")
    p_guess.add_argument("text")

    p_brute = sub.add_parser("brute", help="Brute force")
    p_brute.add_argument("text")
    p_brute.add_argument("-f","--family", action="append", help="Family name (repeatable)", default=[])

    if len(argv)==0:
        # no args: launch GUI if possible, else show help
        if tk is not None:
            launch_gui()
            return 0
        parser.print_help()
        return 0

    args = parser.parse_args(argv)
    if args.cmd == "list":
        for ce in get_registry():
            par = ", ".join(f"{p.name} (default={p.default})" for p in ce.params) or "-"
            print(f"{ce.name:24} params: {par}")
        return 0
    elif args.cmd == "encode":
        params = parse_kv_list(args.param)
        out = call_encode(args.cipher, args.text, params)
        print(out)
        return 0
    elif args.cmd == "decode":
        params = parse_kv_list(args.param)
        out = call_decode(args.cipher, args.text, params)
        print(out)
        return 0
    elif args.cmd == "guess":
        ranked = SmartGuess(args.text)
        for i,(label, pt, sc) in enumerate(ranked, 1):
            print(f"{i:2d}. {label:28} score={sc:8.2f} | {pt[:80].replace('\\n',' ')}")
        return 0
    elif args.cmd == "brute":
        fams = args.family or ["caesar","affine","railfence","vigenere-short","xor-hex"]
        ranked = BruteForce(args.text, fams)
        for i,(label, pt, sc) in enumerate(ranked, 1):
            print(f"{i:2d}. {label:28} score={sc:8.2f} | {pt[:80].replace('\\n',' ')}")
        return 0
    else:
        parser.print_help()
        return 0

# =============================================================================
# GUI (Tkinter) — with QoL improvements
# =============================================================================

APP_STATE_FILE = str(Path.home() / ".all_the_ciphers_gui.json")

class CipherGUI:
    def __init__(self, root: tk.Tk):
        self.root = root
        root.title("All-The-Ciphers")
        root.geometry("1100x720")

        self.dark = False
        self.font_size = 12

        self.registry = get_registry()
        self.name_to_entry = {ce.name: ce for ce in self.registry}

        self._build_menu()
        self._build_layout()
        self._bind_keys()
        self._load_state()
        self._apply_theme()

        self._update_status()

    # --- UI build

    def _build_menu(self):
        m = tk.Menu(self.root)
        self.root.config(menu=m)

        fm = tk.Menu(m, tearoff=0)
        fm.add_command(label="Open…  (Ctrl+O)", command=self.open_file)
        fm.add_command(label="Save Output…  (Ctrl+S)", command=self.save_output)
        fm.add_separator()
        fm.add_command(label="Exit", command=self.root.destroy)
        m.add_cascade(label="File", menu=fm)

        em = tk.Menu(m, tearoff=0)
        em.add_command(label="Copy Output", command=self.copy_output)
        em.add_command(label="Paste to Input", command=self.paste_input)
        em.add_command(label="Swap In/Out  (Ctrl+I)", command=self.swap_io)
        m.add_cascade(label="Edit", menu=em)

        tm = tk.Menu(m, tearoff=0)
        tm.add_command(label="Toggle Dark Mode", command=self.toggle_dark)
        tm.add_command(label="Bigger Font", command=lambda: self.adjust_font(1))
        tm.add_command(label="Smaller Font", command=lambda: self.adjust_font(-1))
        m.add_cascade(label="View", menu=tm)

        hm = tk.Menu(m, tearoff=0)
        hm.add_command(label="About", command=self.show_about)
        m.add_cascade(label="Help", menu=hm)

    def _build_layout(self):
        # Top row: cipher selector + params
        top = ttk.Frame(self.root)
        top.pack(side="top", fill="x", padx=8, pady=6)

        ttk.Label(top, text="Cipher:").pack(side="left")
        self.cipher_var = tk.StringVar(value=self.registry[0].name)
        self.cipher_cb = ttk.Combobox(top, textvariable=self.cipher_var, values=[ce.name for ce in self.registry], state="readonly", width=26)
        self.cipher_cb.pack(side="left", padx=6)
        self.cipher_cb.bind("<<ComboboxSelected>>", lambda e: self._rebuild_params())

        self.mode_var = tk.StringVar(value="encode")
        ttk.Radiobutton(top, text="Encode", variable=self.mode_var, value="encode").pack(side="left", padx=4)
        ttk.Radiobutton(top, text="Decode", variable=self.mode_var, value="decode").pack(side="left", padx=4)

        self.run_btn = ttk.Button(top, text="Run (Ctrl+E / Ctrl+D)", command=self.run_current)
        self.run_btn.pack(side="left", padx=8)

        ttk.Separator(self.root, orient="horizontal").pack(fill="x", pady=4)

        # Params row (dynamic)
        self.params_frame = ttk.Frame(self.root)
        self.params_frame.pack(side="top", fill="x", padx=8, pady=6)
        self.param_vars: Dict[str, tk.StringVar] = {}
        self._rebuild_params()

        # Middle: text areas + side buttons
        mid = ttk.Frame(self.root)
        mid.pack(side="top", fill="both", expand=True, padx=8, pady=6)

        self.input_txt = tk.Text(mid, wrap="word", height=12, undo=True)
        self.output_txt = tk.Text(mid, wrap="word", height=12, undo=True)

        self.input_txt.pack(side="left", fill="both", expand=True, padx=(0,4))
        right = ttk.Frame(mid); right.pack(side="left", fill="y")
        self.output_txt.pack(side="left", fill="both", expand=True, padx=(4,0))

        ttk.Button(right, text="Smart Guess (Ctrl+G)", command=self.smart_guess).pack(fill="x", pady=2)
        ttk.Button(right, text="Brute Force (Ctrl+B)", command=self.brute_force).pack(fill="x", pady=2)
        ttk.Separator(right, orient="horizontal").pack(fill="x", pady=4)
        ttk.Button(right, text="Swap In/Out (Ctrl+I)", command=self.swap_io).pack(fill="x", pady=2)
        ttk.Button(right, text="Copy Output", command=self.copy_output).pack(fill="x", pady=2)
        ttk.Button(right, text="Paste → Input", command=self.paste_input).pack(fill="x", pady=2)
        ttk.Button(right, text="Clear Both (Ctrl+L)", command=self.clear_both).pack(fill="x", pady=2)
        ttk.Separator(right, orient="horizontal").pack(fill="x", pady=4)
        ttk.Button(right, text="Open… (Ctrl+O)", command=self.open_file).pack(fill="x", pady=2)
        ttk.Button(right, text="Save Output… (Ctrl+S)", command=self.save_output).pack(fill="x", pady=2)
        ttk.Separator(right, orient="horizontal").pack(fill="x", pady=4)
        ttk.Button(right, text="Dark Mode", command=self.toggle_dark).pack(fill="x", pady=2)

        # Bottom: status
        self.status = ttk.Label(self.root, text="Ready", anchor="w")
        self.status.pack(side="bottom", fill="x")

        # events for status updates
        self.input_txt.bind("<<Modified>>", self._on_text_change)
        self.output_txt.bind("<<Modified>>", self._on_text_change)

        # Auto-detect: if tagged input, switch to Decode automatically when focusing output
        self.input_txt.bind("<FocusOut>", lambda e: self._auto_select_decoder())

        # Apply font size
        self._apply_font()

    def _rebuild_params(self):
        for w in self.params_frame.winfo_children():
            w.destroy()
        self.param_vars.clear()
        ce = self.name_to_entry[self.cipher_var.get()]
        if not ce.params:
            ttk.Label(self.params_frame, text="(No parameters)").pack(side="left")
            return
        for p in ce.params:
            ttk.Label(self.params_frame, text=p.label+":").pack(side="left", padx=(0,3))
            var = tk.StringVar(value=p.default)
            ent = ttk.Entry(self.params_frame, textvariable=var, width=max(8, len(p.default)+2))
            ent.pack(side="left", padx=(0,12))
            if p.tip:
                ent.tooltip = p.tip
            self.param_vars[p.name] = var

    def _bind_keys(self):
        self.root.bind("<Control-e>", lambda e: self._set_mode_and_run("encode"))
        self.root.bind("<Control-d>", lambda e: self._set_mode_and_run("decode"))
        self.root.bind("<Control-g>", lambda e: self.smart_guess())
        self.root.bind("<Control-b>", lambda e: self.brute_force())
        self.root.bind("<Control-l>", lambda e: self.clear_both())
        self.root.bind("<Control-i>", lambda e: self.swap_io())
        self.root.bind("<Control-o>", lambda e: self.open_file())
        self.root.bind("<Control-s>", lambda e: self.save_output())

    # --- Theme / State

    def _apply_font(self):
        f = ("Consolas", self.font_size)
        self.input_txt.configure(font=f)
        self.output_txt.configure(font=f)

    def _apply_theme(self):
        if self.dark:
            bg = "#0f1116"; fg = "#e6edf3"; acc = "#1f6feb"
            self.root.configure(bg=bg)
            for w in (self.input_txt, self.output_txt):
                w.configure(bg="#161b22", fg=fg, insertbackground=fg)
            style = ttk.Style()
            try:
                style.theme_use('clam')
            except:
                pass
            style.configure(".", background=bg, foreground=fg)
            style.configure("TButton", background="#21262d", foreground=fg)
            style.configure("TLabel", background=bg, foreground=fg)
            style.configure("TFrame", background=bg)
            style.configure("TEntry", fieldbackground="#161b22", foreground=fg)
            self.status.configure(background="#0b0d12", foreground=fg)
        else:
            # system default
            for w in (self.input_txt, self.output_txt):
                w.configure(bg="white", fg="black", insertbackground="black")
            style = ttk.Style()
            style.theme_use(style.theme_use())
            self.status.configure(background="", foreground="")

    def toggle_dark(self):
        self.dark = not self.dark
        self._apply_theme()
        self._save_state()

    def adjust_font(self, delta: int):
        self.font_size = max(8, min(24, self.font_size + delta))
        self._apply_font()
        self._save_state()

    def _state_dict(self) -> Dict[str, object]:
        return {
            "cipher": self.cipher_var.get(),
            "mode": self.mode_var.get(),
            "dark": self.dark,
            "font_size": self.font_size,
            "params": {k:v.get() for k,v in self.param_vars.items()},
            "input": self.input_txt.get("1.0", "end-1c"),
            "output": self.output_txt.get("1.0", "end-1c"),
        }

    def _apply_state(self, st: Dict[str, object]):
        if not st: return
        if "cipher" in st and st["cipher"] in self.name_to_entry:
            self.cipher_var.set(st["cipher"]); self._rebuild_params()
        if "mode" in st:
            self.mode_var.set(st["mode"])
        self.dark = bool(st.get("dark", False))
        self.font_size = int(st.get("font_size", 12))
        if "params" in st:
            for k,v in st["params"].items():
                if k in self.param_vars:
                    self.param_vars[k].set(v)
        if "input" in st:
            self.input_txt.delete("1.0","end"); self.input_txt.insert("1.0", st["input"])
        if "output" in st:
            self.output_txt.delete("1.0","end"); self.output_txt.insert("1.0", st["output"])

    def _save_state(self):
        try:
            with open(APP_STATE_FILE, "w", encoding="utf-8") as f:
                json.dump(self._state_dict(), f, ensure_ascii=False, indent=2)
        except Exception as e:
            # non-fatal
            pass

    def _load_state(self):
        try:
            if os.path.exists(APP_STATE_FILE):
                with open(APP_STATE_FILE, "r", encoding="utf-8") as f:
                    st = json.load(f)
                    self._apply_state(st)
        except Exception:
            pass

    # --- Actions

    def _read_params(self) -> Dict[str,str]:
        out = {}
        for k,var in self.param_vars.items():
            out[k] = var.get()
        return out

    def run_current(self):
        name = self.cipher_var.get()
        text = self.input_txt.get("1.0", "end-1c")
        params = self._read_params()
        t0 = time.time()
        try:
            if self.mode_var.get() == "encode":
                out = call_encode(name, text, params)
            else:
                out = call_decode(name, text, params)
        except Exception as e:
            out = f"Err:{e}"
        dt = (time.time()-t0)*1000
        self.output_txt.delete("1.0","end")
        self.output_txt.insert("1.0", out)
        self._status_ok(f"{name} {self.mode_var.get()} in {dt:.1f} ms")
        self._save_state()

    def _set_mode_and_run(self, mode: str):
        self.mode_var.set(mode)
        self.run_current()

    def smart_guess(self):
        text = self.input_txt.get("1.0", "end-1c")
        ranked = SmartGuess(text)
        self._show_ranked_window("Smart Guess — Top Candidates", ranked)

    def brute_force(self):
        text = self.input_txt.get("1.0", "end-1c")
        fams = self._ask_families()
        if fams is None: return
        ranked = BruteForce(text, fams)
        self._show_ranked_window("Brute Force — Top Candidates", ranked)

    def _ask_families(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("Choose families")
        dlg.geometry("320x260")
        fams = [("caesar","Caesar"), ("affine","Affine"), ("railfence","Rail Fence"), ("vigenere-short","Vigenère (short keys)"), ("xor-hex","XOR hex (single byte)")]
        vars = []
        for key, label in fams:
            v = tk.BooleanVar(value=True)
            chk = ttk.Checkbutton(dlg, text=label, variable=v)
            chk.pack(anchor="w", padx=10, pady=4)
            vars.append((key,v))
        out = []
        def ok():
            out.clear()
            out.extend([k for k,v in vars if v.get()])
            dlg.destroy()
        ttk.Button(dlg, text="Run", command=ok).pack(pady=8)
        dlg.grab_set(); self.root.wait_window(dlg)
        return out if out else None

    def _show_ranked_window(self, title: str, ranked: List[Tuple[str,str,float]]):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.geometry("900x500")
        columns = ("rank","label","score","preview")
        tree = ttk.Treeview(win, columns=columns, show="headings")
        for c, w in zip(columns, (60, 260, 100, 420)):
            tree.heading(c, text=c.capitalize())
            tree.column(c, width=w, anchor="w")
        tree.pack(fill="both", expand=True)

        for i,(label, pt, sc) in enumerate(ranked, 1):
            preview = pt.replace("\n"," ")[:160]
            tree.insert("", "end", values=(i, label, f"{sc:.2f}", preview))

        def use_selection():
            sel = tree.selection()
            if not sel: return
            vals = tree.item(sel[0], "values")
            rank_idx = int(vals[0]) - 1
            _, pt, _ = ranked[rank_idx]
            self.output_txt.delete("1.0","end")
            self.output_txt.insert("1.0", pt)
            self._status_ok(f"Loaded candidate #{rank_idx+1} into Output")

        btns = ttk.Frame(win); btns.pack(fill="x")
        ttk.Button(btns, text="Use Selected → Output", command=use_selection).pack(side="left", padx=6, pady=6)
        ttk.Button(btns, text="Close", command=win.destroy).pack(side="right", padx=6, pady=6)

    def copy_output(self):
        text = self.output_txt.get("1.0","end-1c")
        self.root.clipboard_clear(); self.root.clipboard_append(text)
        self._status_ok("Output copied")

    def paste_input(self):
        try:
            text = self.root.clipboard_get()
        except Exception:
            text = ""
        self.input_txt.delete("1.0","end"); self.input_txt.insert("1.0", text)
        self._status_ok("Pasted to input")

    def swap_io(self):
        inp = self.input_txt.get("1.0","end-1c")
        out = self.output_txt.get("1.0","end-1c")
        self.input_txt.delete("1.0","end"); self.input_txt.insert("1.0", out)
        self.output_txt.delete("1.0","end"); self.output_txt.insert("1.0", inp)
        self._status_ok("Swapped input/output")
        self._save_state()

    def clear_both(self):
        self.input_txt.delete("1.0","end")
        self.output_txt.delete("1.0","end")
        self._status_ok("Cleared")

    def open_file(self):
        try:
            from tkinter import filedialog
            path = filedialog.askopenfilename(title="Open text", filetypes=[("Text files","*.txt *.log *.cfg *.json *.md"), ("All files","*.*")])
            if not path: return
            with open(path, "r", encoding="utf-8", errors="replace") as f:
                data = f.read()
            self.input_txt.delete("1.0","end"); self.input_txt.insert("1.0", data)
            self._status_ok(f"Opened {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Open Failed", str(e))

    def save_output(self):
        try:
            from tkinter import filedialog
            path = filedialog.asksaveasfilename(title="Save output", defaultextension=".txt", filetypes=[("Text files","*.txt"), ("All files","*.*")])
            if not path: return
            data = self.output_txt.get("1.0","end-1c")
            with open(path, "w", encoding="utf-8") as f:
                f.write(data)
            self._status_ok(f"Saved {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Save Failed", str(e))

    def show_about(self):
        messagebox.showinfo("About", "All-The-Ciphers — full suite with Smart Guess & Brute Force\n© You + ChatGPT\nHotkeys: Ctrl+E / Ctrl+D / Ctrl+G / Ctrl+B / Ctrl+I / Ctrl+L / Ctrl+O / Ctrl+S")

    # --- Helpers

    def _status_ok(self, msg: str):
        self.status.config(text=msg)

    def _on_text_change(self, event):
        widget = event.widget
        widget.edit_modified(False)
        self._update_status()

    def _update_status(self):
        a = len(self.input_txt.get("1.0","end-1c"))
        b = len(self.output_txt.get("1.0","end-1c"))
        self.status.config(text=f"Input: {a} chars    Output: {b} chars")

    def _auto_select_decoder(self):
        # If input starts with known tag, flip to decode and pick the right cipher
        s = self.input_txt.get("1.0","end-1c").lstrip()
        tag_map = {
            "[HOMO]": "Homophonic",
            "[EMOJI]": "Emoji Substitution",
            "[WS]": "Whitespace Encoding",
            "[FM]": "Fractionated Morse",
            "[MORSE]": "Morse",
            "[PIG]": "Pigpen",
            "[PL]": "Pig Latin",
            "[SEM]": "Semaphore",
            "[LEET]": "Leet Speak",
        }
        for tag, name in tag_map.items():
            if s.startswith(tag) and name in self.name_to_entry:
                self.cipher_var.set(name)
                self._rebuild_params()
                self.mode_var.set("decode")
                self._status_ok(f"Detected tag {tag} → {name} (Decode)")
                return

# -----------------------------------------------------------------------------

def launch_gui():
    if tk is None:
        print("Tkinter is not available on this system.")
        sys.exit(1)
    root = tk.Tk()
    CipherGUI(root)
    root.mainloop()

# =============================================================================
# Self-test (light) — optional quick sanity on a few ciphers
# =============================================================================

def _selftest():
    tests = [
        ("Caesar", "encode", {"shift":"3"}, "HELLO WORLD", "KHOOR ZRUOG"),
        ("ROT13", "encode", {}, "HELLO", "URYYB"),
        ("Atbash", "encode", {}, "HELLO", "SVOOL"),
        ("Vigenere", "encode", {"key":"LEMON"}, "ATTACKATDAWN", "LXFOPVEFRNHR"),
        ("Rail Fence", "encode", {"rails":"3"}, "WEAREDISCOVEREDFLEEATONCE", "WECRLTEERDSOEEFEAOCAIVDEN"),
        ("ADFGX", "encode", {"square_key":"KEYWORD", "route_key":"CIPHER"}, "ATTACKATDAWN", None),
        ("Baconian", "encode", {}, "HELLO", None),
        ("Playfair", "encode", {"key":"KEYWORD"}, "HELLOWORLD", None),
        ("Emoji Substitution", "encode", {"seed":"SEED"}, "hello world", None),
        ("Whitespace Encoding", "encode", {}, "Hi", None),
        ("Fractionated Morse", "encode", {"key":"KEYABCDFGHIJLMNOPQRSTUVWXZ"}, "SOS", None),
    ]
    ok = 0
    for name, mode, params, pt, expect in tests:
        try:
            if mode=="encode":
                ct = call_encode(name, pt, params)
                if expect is None or ct.startswith(expect) or expect in ct:
                    ok += 1
            else:
                out = call_decode(name, pt, params)
                if expect is None or out == expect:
                    ok += 1
        except Exception as e:
            pass
    return ok, len(tests)

# =============================================================================
# ANALYSIS & SCORING EXTENSIONS
# Frequency graphs, Kasiski/Friedman aids, N-gram scoring sliders
# (Safe to drop before the main guard; this patches the existing GUI.)
# =============================================================================

from collections import Counter, defaultdict
import math

# --- Optional plotting (embedded in Tk) --------------------------------------
try:
    import matplotlib
    matplotlib.use("Agg")  # headless-safe; we'll embed via FigureCanvasTkAgg
    from matplotlib.figure import Figure
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    _HAS_MPL = True
except Exception:
    _HAS_MPL = False

# =============================================================================
# N-GRAM SCORING (good English model, fast, tunable)
# =============================================================================

# Unigram probabilities (roughly English letter freq, A-Z only; normalized)
_UNI = {
    'E':0.12702,'T':0.09056,'A':0.08167,'O':0.07507,'I':0.06966,'N':0.06749,
    'S':0.06327,'H':0.06094,'R':0.05987,'D':0.04253,'L':0.04025,'C':0.02782,
    'U':0.02758,'M':0.02406,'W':0.02360,'F':0.02228,'G':0.02015,'Y':0.01974,
    'P':0.01929,'B':0.01492,'V':0.00978,'K':0.00772,'J':0.00153,'X':0.00150,
    'Q':0.00095,'Z':0.00074
}
# Bigram: a compact list of common ones (rest backoff to floor)
# Values are *relative*; we turn them into log-probs with smoothing.
_BI = {
    "TH":1.52,"HE":1.28,"IN":0.94,"ER":0.94,"AN":0.82,"RE":0.68,"ND":0.63,
    "AT":0.59,"ON":0.57,"NT":0.56,"HA":0.56,"ES":0.56,"ST":0.55,"EN":0.55,
    "ED":0.53,"TO":0.52,"IT":0.50,"OU":0.50,"EA":0.47,"HI":0.46,"IS":0.46,
    "OR":0.43,"TI":0.34,"AS":0.33,"TE":0.27,"ET":0.19,"NG":0.18,"OF":0.16
}
# Trigram: top frequent in English
_TRI = {
    "THE":1.81,"AND":0.73,"ING":0.72,"ION":0.42,"ENT":0.42,"HER":0.36,"FOR":0.34,
    "THA":0.33,"NTH":0.33,"INT":0.32,"ERE":0.31,"TIO":0.31,"TER":0.30,"EST":0.28,
    "ERS":0.28,"ATI":0.26,"HAT":0.26,"ATE":0.25,"ALL":0.25,"ETH":0.24,"HES":0.24
}

# Defaults: reasonably strong weight on tri/bi, lighter on uni.
_NGRAM_WEIGHTS = {1: 0.6, 2: 1.0, 3: 1.6}
# Floor log-prob for unseen n-grams. (Raise toward  -6  to be less penalizing.)
_NGRAM_FLOOR_LOGP = -8.5

# Build log tables (once). Unigram gets true log probs; bi/tri are scaled then log.
def _logp_tables():
    uni = {k: math.log(v) for k, v in _UNI.items()}
    # normalize BI/TRI rough counts -> probs (sum to 1 of listed items)
    def _to_logp(d):
        s = sum(d.values())
        return {k: math.log(v/s) for k,v in d.items()}
    return uni, _to_logp(_BI), _to_logp(_TRI)
_LOG_UNI, _LOG_BI, _LOG_TRI = _logp_tables()

def set_ngram_weights(w1: float = None, w2: float = None, w3: float = None, floor_logp: float = None):
    """Update n-gram weights or floor. Any None leaves current value."""
    global _NGRAM_WEIGHTS, _NGRAM_FLOOR_LOGP
    if w1 is not None: _NGRAM_WEIGHTS[1] = float(w1)
    if w2 is not None: _NGRAM_WEIGHTS[2] = float(w2)
    if w3 is not None: _NGRAM_WEIGHTS[3] = float(w3)
    if floor_logp is not None: _NGRAM_FLOOR_LOGP = float(floor_logp)

def get_ngram_weights():
    return dict(_NGRAM_WEIGHTS), _NGRAM_FLOOR_LOGP

def _letters_only(s: str) -> str:
    return "".join(ch for ch in s.upper() if 'A' <= ch <= 'Z')

def score_english_ngram(text: str) -> float:
    """Return a *higher is better* score based on uni/bi/tri log-prob sums."""
    s = _letters_only(text)
    n = len(s)
    if n == 0:
        return -1e9
    w1, w2, w3 = _NGRAM_WEIGHTS.get(1,1.0), _NGRAM_WEIGHTS.get(2,1.0), _NGRAM_WEIGHTS.get(3,1.0)

    # Unigram score
    su = 0.0
    for ch in s:
        su += _LOG_UNI.get(ch, _NGRAM_FLOOR_LOGP)

    # Bigram
    sb = 0.0
    for i in range(n-1):
        bg = s[i:i+2]
        sb += _LOG_BI.get(bg, _NGRAM_FLOOR_LOGP)

    # Trigram
    st = 0.0
    for i in range(n-2):
        tg = s[i:i+3]
        st += _LOG_TRI.get(tg, _NGRAM_FLOOR_LOGP)

    # Combine (weights)
    return w1*su + w2*sb + w3*st

# Try to make existing guessers use this automatically (covers common names).
globals()['ENGLISH_SCORE_FN'] = score_english_ngram
globals()['english_score']   = score_english_ngram
globals()['score_english']   = score_english_ngram
globals()['ScoreEnglish']    = score_english_ngram

# =============================================================================
# IC / Friedman; Kasiski examination
# =============================================================================

def index_of_coincidence(text: str) -> float:
    s = _letters_only(text)
    N = len(s)
    if N < 2: return 0.0
    counts = Counter(s)
    num = sum(c*(c-1) for c in counts.values())
    den = N*(N-1)
    return num/den if den else 0.0

def friedman_estimate_keylen(text: str) -> float:
    """Classic Friedman estimate for Vigenère key length (float)."""
    s = _letters_only(text)
    N = len(s)
    if N < 2:
        return 1.0
    IC = index_of_coincidence(s)
    # Using standard constants for English
    K0 = 0.0385
    K1 = 0.065
    if IC <= 0: return 1.0
    num = (K1 - K0) * N
    den = (N - 1) * IC - K0*N + K1
    if den <= 0:
        return 1.0
    return num/den

def split_cosets(s: str, m: int) -> list[str]:
    return ["".join(s[i] for i in range(j, len(s), m)) for j in range(m)]

def friedman_by_keylen(text: str, max_m: int = 20) -> list[tuple[int,float]]:
    s = _letters_only(text)
    out = []
    for m in range(1, max_m+1):
        cosets = split_cosets(s, m)
        ics = [index_of_coincidence(c) for c in cosets if len(c) > 1]
        avg_ic = sum(ics)/len(ics) if ics else 0.0
        out.append((m, avg_ic))
    # Sort by how close to ~0.065; could also rank by avg_ic desc
    out.sort(key=lambda t: abs(0.065 - t[1]))
    return out

def kasiski_examination(text: str, ngram_min: int = 3, ngram_max: int = 5, max_key: int = 20):
    """
    Return:
      repeats: list of (ngram, positions, distances)
      factors: Counter of factor frequencies (2..max_key)
    """
    s = _letters_only(text)
    pos_map = defaultdict(list)
    for n in range(ngram_min, ngram_max+1):
        for i in range(0, len(s)-n+1):
            gram = s[i:i+n]
            pos_map[gram].append(i)
    repeats = []
    for gram, pos in pos_map.items():
        if len(pos) >= 2:
            dists = []
            for i in range(1, len(pos)):
                dists.append(pos[i] - pos[i-1])
            if dists:
                repeats.append((gram, pos, dists))
    # Factor histogram
    fac = Counter()
    for _,_,dists in repeats:
        for d in dists:
            for k in range(2, max_key+1):
                if d % k == 0:
                    fac[k] += 1
    return repeats, fac

# =============================================================================
# GUI PATCHES: Tools menu, windows, sliders, and SmartGuess/BruteForce sync
# =============================================================================

def _format_pct(v: float) -> str:
    return f"{v*100:.2f}%"

def _mk_table(parent, columns, widths):
    tree = ttk.Treeview(parent, columns=columns, show="headings")
    for col, w in zip(columns, widths):
        tree.heading(col, text=col)
        tree.column(col, width=w, anchor="w")
    return tree

def _ngram_freqs(s: str):
    s = _letters_only(s)
    uni = Counter(s)
    bi = Counter(s[i:i+2] for i in range(len(s)-1))
    tri = Counter(s[i:i+3] for i in range(len(s)-2))
    return uni, bi, tri, len(s)

def _plot_bar(ax, labels, values, title):
    ax.clear()
    ax.bar(labels, values)
    ax.set_title(title)
    ax.set_ylim(0, max(values+[1]))
    ax.grid(True, axis="y", alpha=0.3)

def _install_tools_menu(self):
    try:
        m = self.root.nametowidget(self.root['menu'])
    except Exception:
        return
    tools = tk.Menu(m, tearoff=0)
    tools.add_command(label="Frequencies… (Ctrl+F)", command=self.open_freq_window)
    tools.add_command(label="Kasiski/Friedman… (Ctrl+K)", command=self.open_kasiski_window)
    tools.add_separator()
    tools.add_command(label="Scoring Weights… (Ctrl+T)", command=self.open_scoring_window)
    # NEW:
    tools.add_separator()
    tools.add_command(label="Test Bench…", command=lambda: _open_test_bench(self))
    m.add_cascade(label="Tools", menu=tools)


def _gui_open_freq_window(self):
    win = tk.Toplevel(self.root)
    win.title("Frequency Analysis")
    win.geometry("920x640")

    top = ttk.Frame(win); top.pack(fill="x", padx=8, pady=8)
    ttk.Label(top, text="Source:").pack(side="left")
    src = tk.StringVar(value="Input")
    ttk.Radiobutton(top, text="Input", variable=src, value="Input").pack(side="left", padx=6)
    ttk.Radiobutton(top, text="Output", variable=src, value="Output").pack(side="left", padx=6)

    if not _HAS_MPL:
        ttk.Label(win, text="matplotlib not available. Install it to see charts.").pack(pady=16)
        return

    fig = Figure(figsize=(9.2, 4.8))
    ax1 = fig.add_subplot(3,1,1)
    ax2 = fig.add_subplot(3,1,2)
    ax3 = fig.add_subplot(3,1,3)

    canvas = FigureCanvasTkAgg(fig, master=win)
    canvas.get_tk_widget().pack(fill="both", expand=True, padx=8, pady=8)

    info = tk.Text(win, height=6, wrap="word"); info.pack(fill="x", padx=8, pady=(0,8))

    def refresh():
        text = self.input_txt.get("1.0","end-1c") if src.get()=="Input" else self.output_txt.get("1.0","end-1c")
        uni, bi, tri, N = _ngram_freqs(text)

        # Normalize to percentages for unigrams
        letters = [chr(i) for i in range(ord('A'), ord('Z')+1)]
        vals = [100.0*uni.get(ch,0)/max(1,N) for ch in letters]

        # Top 20 bigrams/trigrams
        top_bi = bi.most_common(20)
        top_tri = tri.most_common(20)
        bi_labels = [k for k,_ in top_bi] or ["(none)"]
        bi_vals   = [v for _,v in top_bi] or [0]
        tri_labels = [k for k,_ in top_tri] or ["(none)"]
        tri_vals   = [v for _,v in top_tri] or [0]

        _plot_bar(ax1, letters, vals, f"Letters (%) — N={N}")
        _plot_bar(ax2, bi_labels, bi_vals, "Top 20 Bigrams (counts)")
        _plot_bar(ax3, tri_labels, tri_vals, "Top 20 Trigrams (counts)")
        fig.tight_layout()
        canvas.draw()

        ic = index_of_coincidence(text)
        est = friedman_estimate_keylen(text)
        info.delete("1.0","end")
        info.insert("1.0", f"Index of Coincidence: {ic:.5f}\nFriedman Estimated Key Length: {est:.2f}\n")
        # Add a quick English/uniform ref
        info.insert("end", "Reference: English IC≈0.065, Uniform IC≈0.0385\n")

    btn = ttk.Button(top, text="Analyze", command=refresh)
    btn.pack(side="right")
    refresh()  # initial

def _gui_open_kasiski_window(self):
    win = tk.Toplevel(self.root)
    win.title("Kasiski + Friedman Aids")
    win.geometry("960x640")

    top = ttk.Frame(win); top.pack(fill="x", padx=8, pady=8)
    ttk.Label(top, text="Analyze from:").pack(side="left")
    src = tk.StringVar(value="Input")
    ttk.Radiobutton(top, text="Input", variable=src, value="Input").pack(side="left", padx=6)
    ttk.Radiobutton(top, text="Output", variable=src, value="Output").pack(side="left", padx=6)

    nmin = tk.IntVar(value=3); nmax = tk.IntVar(value=5); kmax = tk.IntVar(value=20)
    for lbl, var in (("n-min", nmin),("n-max", nmax),("max key", kmax)):
        ttk.Label(top, text=f"{lbl}:").pack(side="left", padx=(12,3))
        ttk.Entry(top, textvariable=var, width=4).pack(side="left")

    btn = ttk.Button(top, text="Run", command=lambda: run())
    btn.pack(side="right")

    # Tables
    mid = ttk.Frame(win); mid.pack(fill="both", expand=True, padx=8, pady=8)
    left = ttk.Frame(mid); left.pack(side="left", fill="both", expand=True)
    right = ttk.Frame(mid); right.pack(side="left", fill="both", expand=True, padx=(8,0))

    t_rep = _mk_table(left, ("ngram","positions","distances"), (160,220,220))
    t_rep.pack(fill="both", expand=True)
    ttk.Label(left, text="Repeating n-grams (positions, consecutive distances)").pack(anchor="w", pady=(4,0))

    t_fac = _mk_table(right, ("key_len","votes"), (120,100))
    t_fac.pack(fill="both", expand=True)
    ttk.Label(right, text="Factor votes (Kasiski)").pack(anchor="w", pady=(4,0))

    # Friedman detailed
    bot = ttk.Frame(win); bot.pack(fill="x", padx=8, pady=(0,8))
    t_fr = _mk_table(bot, ("key_len","avg_IC","Δ|IC-0.065|"), (120,120,140))
    t_fr.pack(fill="x")
    ttk.Label(win, text="Friedman by key length (sorted by closeness to English IC)").pack(anchor="w", padx=8)

    def run():
        text = self.input_txt.get("1.0","end-1c") if src.get()=="Input" else self.output_txt.get("1.0","end-1c")
        repeats, fac = kasiski_examination(text, ngram_min=nmin.get(), ngram_max=nmax.get(), max_key=kmax.get())
        # Fill repeats (limit for sanity)
        t_rep.delete(*t_rep.get_children())
        for gram, pos, dists in sorted(repeats, key=lambda r: (-len(r[2]), r[0]))[:80]:
            t_rep.insert("", "end", values=(gram, ", ".join(map(str,pos[:10])) + (" ..." if len(pos)>10 else ""),
                                            ", ".join(map(str,dists[:10])) + (" ..." if len(dists)>10 else "")))

        t_fac.delete(*t_fac.get_children())
        # Show top by votes
        for k, v in fac.most_common(20):
            t_fac.insert("", "end", values=(k, v))

        # Friedman sweep
        t_fr.delete(*t_fr.get_children())
        fr = friedman_by_keylen(text, max_m=kmax.get())
        for m, ic in fr[:25]:
            t_fr.insert("", "end", values=(m, f"{ic:.5f}", f"{abs(0.065-ic):.5f}"))

    run()

def _gui_open_scoring_window(self):
    win = tk.Toplevel(self.root)
    win.title("Scoring Weights (Smart Guess & Brute Force)")
    win.geometry("520x320")

    cur_w, cur_floor = get_ngram_weights()

    frm = ttk.Frame(win); frm.pack(fill="both", expand=True, padx=12, pady=12)

    ttk.Label(frm, text="Unigram weight").grid(row=0, column=0, sticky="w")
    s1 = tk.DoubleVar(value=cur_w.get(1,0.6))
    w1 = ttk.Scale(frm, from_=0.0, to=3.0, orient="horizontal", variable=s1)
    w1.grid(row=0, column=1, sticky="ew", padx=8)

    ttk.Label(frm, text="Bigram weight").grid(row=1, column=0, sticky="w")
    s2 = tk.DoubleVar(value=cur_w.get(2,1.0))
    w2 = ttk.Scale(frm, from_=0.0, to=4.0, orient="horizontal", variable=s2)
    w2.grid(row=1, column=1, sticky="ew", padx=8)

    ttk.Label(frm, text="Trigram weight").grid(row=2, column=0, sticky="w")
    s3 = tk.DoubleVar(value=cur_w.get(3,1.6))
    w3 = ttk.Scale(frm, from_=0.0, to=5.0, orient="horizontal", variable=s3)
    w3.grid(row=2, column=1, sticky="ew", padx=8)

    ttk.Label(frm, text="Floor log-prob (unseen grams)").grid(row=3, column=0, sticky="w")
    sf = tk.DoubleVar(value=cur_floor)
    wf = ttk.Scale(frm, from_=-12.0, to=-4.0, orient="horizontal", variable=sf)
    wf.grid(row=3, column=1, sticky="ew", padx=8)

    frm.columnconfigure(1, weight=1)

    out = ttk.Label(frm, text="")
    out.grid(row=4, column=0, columnspan=2, pady=(12,0), sticky="w")

    def apply_now():
        set_ngram_weights(s1.get(), s2.get(), s3.get(), sf.get())
        # Make sure Smart Guess / Brute Force will pick the scorer
        globals()['ENGLISH_SCORE_FN'] = score_english_ngram
        globals()['english_score']   = score_english_ngram
        globals()['score_english']   = score_english_ngram
        globals()['ScoreEnglish']    = score_english_ngram
        out.config(text=f"Applied: unigram={s1.get():.2f}, bigram={s2.get():.2f}, trigram={s3.get():.2f}, floor={sf.get():.2f}")
        try:
            # persist into the main app state
            self._save_state()
        except Exception:
            pass

    btns = ttk.Frame(win); btns.pack(fill="x", padx=12, pady=(0,12))
    ttk.Button(btns, text="Apply", command=apply_now).pack(side="left")
    ttk.Button(btns, text="Close", command=win.destroy).pack(side="right")

# ---- Patch CipherGUI: add menu, bind keys, extend state persistence ----------

def _patch_bind_keys(self):
    # call original
    try:
        self.__class__._bind_keys_original(self)
    except AttributeError:
        pass
    # New bindings
    self.root.bind("<Control-f>", lambda e: self.open_freq_window())
    self.root.bind("<Control-F>", lambda e: self.open_freq_window())
    self.root.bind("<Control-k>", lambda e: self.open_kasiski_window())
    self.root.bind("<Control-K>", lambda e: self.open_kasiski_window())
    self.root.bind("<Control-t>", lambda e: self.open_scoring_window())
    self.root.bind("<Control-T>", lambda e: self.open_scoring_window())

def _patch_build_menu(self):
    # call original
    try:
        self.__class__._build_menu_original(self)
    except AttributeError:
        pass
    _install_tools_menu(self)

def _state_dict_aug(self):
    # merge into base state dict
    try:
        base = self.__class__._state_dict_original(self)
    except AttributeError:
        base = {}
    w, floor = get_ngram_weights()
    base["ngram_weights"] = w
    base["ngram_floor"] = floor
    return base

def _apply_state_aug(self, st):
    try:
        self.__class__._apply_state_original(self, st)
    except AttributeError:
        pass
    try:
        w = st.get("ngram_weights", None)
        floor = st.get("ngram_floor", None)
        if w:
            set_ngram_weights(w.get(1), w.get(2), w.get(3))
        if floor is not None:
            set_ngram_weights(floor_logp=floor)
    except Exception:
        pass

def _smart_guess_wrap(self):
    # Ensure scorer is active before delegating
    globals()['ENGLISH_SCORE_FN'] = score_english_ngram
    globals()['english_score']   = score_english_ngram
    globals()['score_english']   = score_english_ngram
    globals()['ScoreEnglish']    = score_english_ngram
    # Call the original method (aliased)
    return self.__class__.smart_guess_original(self)

def _brute_force_wrap(self):
    globals()['ENGLISH_SCORE_FN'] = score_english_ngram
    globals()['english_score']   = score_english_ngram
    globals()['score_english']   = score_english_ngram
    globals()['ScoreEnglish']    = score_english_ngram
    return self.__class__.brute_force_original(self)

def install_analysis_extensions():
    """Patch the existing CipherGUI class with new menus, windows, and state."""
    if 'CipherGUI' not in globals():
        return  # nothing to patch yet

    # Attach new window openers
    CipherGUI.open_freq_window = _gui_open_freq_window
    CipherGUI.open_kasiski_window = _gui_open_kasiski_window
    CipherGUI.open_scoring_window = _gui_open_scoring_window

    # Keep originals and patch build_menu/bind_keys/state save+load
    if not hasattr(CipherGUI, "_build_menu_original"):
        CipherGUI._build_menu_original = CipherGUI._build_menu
        CipherGUI._bind_keys_original  = CipherGUI._bind_keys
        CipherGUI._state_dict_original = CipherGUI._state_dict
        CipherGUI._apply_state_original = CipherGUI._apply_state
        CipherGUI.smart_guess_original = CipherGUI.smart_guess
        CipherGUI.brute_force_original = CipherGUI.brute_force

        CipherGUI._build_menu = _patch_build_menu
        CipherGUI._bind_keys  = _patch_bind_keys
        CipherGUI._state_dict = _state_dict_aug
        CipherGUI._apply_state = _apply_state_aug
        CipherGUI.smart_guess = _smart_guess_wrap
        CipherGUI.brute_force = _brute_force_wrap

# Call immediately so main GUI uses the patched version
install_analysis_extensions()

# =============================================================================
# Entrypoint
# =============================================================================
# =============================================================================
# UNIVERSAL KEY-GUESSERS, IOC HEATMAP, RANKED CANDIDATE CAPTURE & EXPORT
# =============================================================================
# This block augments the previously-installed analysis extensions, wiring
# Smart Guess and Brute Force to:
#  - Generate/collect ranked candidates across many cipher families
#  - Display an IOC heatmap and export CSV of candidate lists
#  - Auto-suggest Vigenère/Autokey key lengths and feed them to the GUI
#
# Drop this in after the earlier "Analysis & Scoring Extensions" section.
# =============================================================================
# =============================================================================
# TIME-BOUNDED MONOALPHABETIC SUBSTITUTION + OPTIONS DIALOGS + PRESETS
# Extra guessers (ROT13/47, Playfair(seeded), ADFGX/ADFGVX(heuristic))
# =============================================================================

import math, random, time, json
from collections import Counter
import tkinter as tk
from tkinter import ttk, messagebox
try:
    from tkinter import filedialog as fd
except Exception:
    fd = None

# We will re-point the composite scorer here to allow preset tuning
SCORING_WEIGHTS = {
    "ngram": 1.00,   # main quadgram model (via existing score_english_ngram if available)
    "chi2":  0.20,   # letter-frequency chi^2 fallback
    "word":  0.15,   # common-words presence
    "ioc":   0.05,   # plaintext IC closeness to 0.066
}

COMMON_WORDS = [
    "THE","AND","THAT","HAVE","FOR","NOT","WITH","YOU","THIS","BUT","FROM",
    "THEY","SAY","HER","SHE","OR","WILL","MY","ONE","ALL","WOULD","THERE",
    "THEIR","WHAT","SO","UP","OUT","IF","ABOUT","WHO","GET","WHICH","GO",
    "ME","WHEN","MAKE","CAN","LIKE","TIME","NO","JUST","HIM","KNOW","TAKE",
    "PEOPLE","INTO","YEAR","YOUR","GOOD"
]

# --- If an earlier _score_pt exists, keep a reference --------------------------------
try:
    _old_score_pt = _score_pt
except Exception:
    _old_score_pt = None

def _chi2_score(pt_alpha: str) -> float:
    if not pt_alpha: return -1e9
    freq = Counter(pt_alpha)
    N = len(pt_alpha)
    expected = {
        'E': 12.702, 'T': 9.056, 'A': 8.167, 'O': 7.507, 'I': 6.966, 'N': 6.749,
        'S': 6.327, 'H': 6.094, 'R': 5.987, 'D': 4.253, 'L': 4.025, 'C': 2.782,
        'U': 2.758, 'M': 2.406, 'W': 2.360, 'F': 2.228, 'G': 2.015, 'Y': 1.974,
        'P': 1.929, 'B': 1.492, 'V': 0.978, 'K': 0.772, 'J': 0.153, 'X': 0.150,
        'Q': 0.095, 'Z': 0.074
    }
    chi = 0.0
    for ch in ALPHA:
        o = freq.get(ch,0) * 100.0 / N
        e = expected[ch]
        if e > 0:
            diff = o - e
            chi += (diff*diff)/e
    return -chi

def _ioc_closeness(pt_alpha: str) -> float:
    # reward closeness to typical English (~0.066)
    try:
        ic = index_of_coincidence(pt_alpha)
    except Exception:
        # simple IC
        N = len(pt_alpha)
        if N <= 1: return -1.0
        counts = Counter(pt_alpha)
        num = sum(v*(v-1) for v in counts.values())
        den = N*(N-1)
        ic = num/den if den else 0.0
    return -abs(0.066 - ic)*50.0

def _word_score(pt_upper: str) -> float:
    s = 0.0
    U = " " + pt_upper + " "
    for w in COMMON_WORDS:
        # crude boundaries to avoid counting sub-words in the middle
        c = U.count(" " + w + " ")
        if c:
            s += math.log(1+c) * 8.0
    return s

def _score_pt(pt: str) -> float:
    # Composite scoring under weights, falling back to old scorer if present.
    try:
        pt_upper = pt.upper()
        pt_alpha = _clean_alpha(pt_upper)
        total = 0.0
        if SCORING_WEIGHTS.get("ngram",0) > 0:
            try:
                base = score_english_ngram(pt)  # provided by the main app
            except Exception:
                base = 0.0
            total += SCORING_WEIGHTS["ngram"] * base
        if SCORING_WEIGHTS.get("chi2",0) > 0:
            total += SCORING_WEIGHTS["chi2"] * _chi2_score(pt_alpha)
        if SCORING_WEIGHTS.get("word",0) > 0:
            total += SCORING_WEIGHTS["word"] * _word_score(pt_upper)
        if SCORING_WEIGHTS.get("ioc",0) > 0:
            total += SCORING_WEIGHTS["ioc"] * _ioc_closeness(pt_alpha)
        # slight preference to printable/spacing balance
        bads = sum(1 for ch in pt if ord(ch) < 9)
        total -= bads * 5.0
        return total
    except Exception:
        if _old_score_pt: 
            try: return _old_score_pt(pt)
            except Exception: pass
        return 0.0

# =============================================================================
# OPTIONS STORAGE + MINI DIALOGS
# =============================================================================
DEFAULT_OPTIONS = {
    "Caesar":     {"enabled": True},
    "Affine":     {"enabled": True},
    "Rail Fence": {"enabled": True, "min_rails": 2, "max_rails": 12},
    "Columnar":   {"enabled": True, "min_width": 2, "max_width": 14},
    "Vigenere":   {"enabled": True, "max_len": 16, "top_keys_per_len": 3},
    "Autokey":    {"enabled": True, "max_len": 12, "seed_try": 2},
    "Beaufort":   {"enabled": True, "max_len": 14},
    "Porta":      {"enabled": True, "max_len": 14},
    "ROT13":      {"enabled": True},
    "ROT47":      {"enabled": True},
    "Playfair":   {"enabled": True, "seed_words": "KEYWORD,SECRET,PASSWORD,MONARCHY,EXAMPLE", "max_variants": 8},
    "ADFGX":      {"enabled": True, "square_key": "KEYWORD", "min_klen": 4, "max_klen": 8},
    "ADFGVX":     {"enabled": True, "square_key": "KEYWORD", "min_klen": 4, "max_klen": 8},
    "Substitution": {"enabled": True, "time_sec": 6.0, "restarts": 8, "start_temp": 2.0, "end_temp": 0.05}
}

GUESSER_OPTIONS = json.loads(json.dumps(DEFAULT_OPTIONS))  # deep copy

SCORING_PRESETS = {
    "Balanced": {"ngram":1.00,"chi2":0.20,"word":0.15,"ioc":0.05},
    "Quadgram-heavy": {"ngram":1.20,"chi2":0.10,"word":0.10,"ioc":0.05},
    "Fast (chi² only)": {"ngram":0.00,"chi2":1.00,"word":0.00,"ioc":0.10},
    "Ciphertext-only": {"ngram":0.00,"chi2":0.35,"word":0.00,"ioc":0.25},
}

def apply_scoring_preset(name: str):
    if name not in SCORING_PRESETS:
        messagebox.showerror("Scoring Presets", f"Unknown preset: {name}")
        return
    SCORING_WEIGHTS.update(SCORING_PRESETS[name])

def save_preset_to_file():
    if fd is None:
        messagebox.showerror("Save Preset", "File dialog not available on this system.")
        return
    path = fd.asksaveasfilename(
        title="Save Scoring Preset",
        defaultextension=".json",
        filetypes=[("JSON", "*.json"), ("All files","*.*")]
    )
    if not path: return
    data = {"weights": SCORING_WEIGHTS, "options": GUESSER_OPTIONS}
    with open(path,"w",encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    messagebox.showinfo("Save Preset", f"Saved to:\n{path}")

def load_preset_from_file():
    if fd is None:
        messagebox.showerror("Load Preset", "File dialog not available on this system.")
        return
    path = fd.askopenfilename(
        title="Load Scoring Preset",
        filetypes=[("JSON", "*.json"), ("All files","*.*")]
    )
    if not path: return
    try:
        with open(path,"r",encoding="utf-8") as f:
            data = json.load(f)
        if "weights" in data:
            SCORING_WEIGHTS.update(data["weights"])
        if "options" in data:
            for k,v in data["options"].items():
                if k in GUESSER_OPTIONS and isinstance(v, dict):
                    GUESSER_OPTIONS[k].update(v)
        messagebox.showinfo("Load Preset", "Preset loaded.")
    except Exception as e:
        messagebox.showerror("Load Preset", f"Failed to load: {e}")

# Mini options dialog builder
def _open_options_dialog(self, family: str):
    if family not in GUESSER_OPTIONS:
        messagebox.showerror("Options", f"No options for '{family}'.")
        return
    opts = GUESSER_OPTIONS[family]
    win = tk.Toplevel(self.root)
    win.title(f"{family} Options")
    win.geometry("420x320")
    frm = ttk.Frame(win); frm.pack(fill="both", expand=True, padx=12, pady=12)

    entries = {}
    ttk.Label(frm, text=f"{family} Guesser Settings", font=("TkDefaultFont", 10, "bold")).pack(anchor="w", pady=(0,8))

    # enabled checkbox
    enabled_var = tk.BooleanVar(value=bool(opts.get("enabled", True)))
    ttk.Checkbutton(frm, text="Enable in Smart Guess / Brute Force", variable=enabled_var).pack(anchor="w", pady=(0,10))

    grid = ttk.Frame(frm); grid.pack(fill="x")
    r=0
    for k,v in opts.items():
        if k=="enabled": continue
        ttk.Label(grid, text=k).grid(row=r, column=0, sticky="w", padx=(0,8), pady=3)
        val = tk.StringVar(value=str(v))
        e = ttk.Entry(grid, width=24, textvariable=val)
        e.grid(row=r, column=1, sticky="w", pady=3)
        entries[k] = val
        r += 1

    btns = ttk.Frame(frm); btns.pack(fill="x", pady=(12,0))
    def save():
        opts["enabled"] = bool(enabled_var.get())
        for k,var in entries.items():
            raw = var.get().strip()
            # try numeric conversion when relevant
            if k.lower().endswith(("len","rails","width","klen","variants","restarts")):
                try: opts[k] = int(raw)
                except: pass
            elif "time" in k.lower() or "temp" in k.lower():
                try: opts[k] = float(raw)
                except: pass
            else:
                opts[k] = raw
        win.destroy()
    def defaults():
        GUESSER_OPTIONS[family] = json.loads(json.dumps(DEFAULT_OPTIONS[family]))
        win.destroy()
        _open_options_dialog(self, family)
    ttk.Button(btns, text="Restore Defaults", command=defaults).pack(side="left")
    ttk.Button(btns, text="Save", command=save).pack(side="right")

# attach menu items to open options
def _patch_options_menu(self):
    try:
        m = self.root.nametowidget(self.root['menu'])
    except Exception:
        return
    # Create or find "Analysis" cascade first (from previous patch)
    # Add "Options" and "Presets" submenus
    options_menu = tk.Menu(m, tearoff=0)
    for fam in ["Caesar","Affine","Rail Fence","Columnar","Vigenere","Autokey","Beaufort","Porta",
                "ROT13","ROT47","Playfair","ADFGX","ADFGVX","Substitution"]:
        options_menu.add_command(label=fam, command=lambda f=fam: _open_options_dialog(self, f))
    presets_menu = tk.Menu(m, tearoff=0)
    for name in SCORING_PRESETS.keys():
        presets_menu.add_command(label=name, command=lambda n=name: apply_scoring_preset(n))
    presets_menu.add_separator()
    presets_menu.add_command(label="Save Current…", command=save_preset_to_file)
    presets_menu.add_command(label="Load…", command=load_preset_from_file)

    # Add a new top-level "Options" and "Scoring Presets" under Analysis
    analysis = tk.Menu(m, tearoff=0)
    analysis.add_cascade(label="Options", menu=options_menu)
    analysis.add_cascade(label="Scoring Presets", menu=presets_menu)
    try:
        m.add_cascade(label="Configure", menu=analysis)
    except Exception:
        pass

def install_options_menu():
    if 'CipherGUI' not in globals():
        return
    if not hasattr(CipherGUI, "_build_menu_original_options"):
        CipherGUI._build_menu_original_options = CipherGUI._build_menu
        def _build_menu_wrap(self):
            CipherGUI._build_menu_original_options(self)
            _patch_options_menu(self)
        CipherGUI._build_menu = _build_menu_wrap

install_options_menu()

# =============================================================================
# MONOALPHABETIC SUBSTITUTION (time-bounded SA hill-climb)
# =============================================================================
def _substitution_decrypt(ct: str, mapping: list[int]) -> str:
    # mapping: index of cipher letter (A=0..Z=25) -> plaintext index (0..25)
    out=[]
    for ch in ct:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            i = ord(u) - 65
            p = mapping[i]
            pc = chr(p + (65 if ch.isupper() else 97))
            out.append(pc)
        else:
            out.append(ch)
    return "".join(out)

def _random_mapping() -> list[int]:
    m = list(range(26)); random.shuffle(m); return m

def _freq_init_mapping(ct: str) -> list[int]:
    # map sorted CT frequencies to ETAOIN… ordering
    s = _clean_alpha(ct)
    freq = Counter(s)
    ordered_ct = [k for k,_ in freq.most_common()] + [ch for ch in ALPHA if ch not in freq]
    eta = list("ETAOINSHRDLUCMWFGYPBVKJXQZ")
    while len(ordered_ct) < 26:
        ordered_ct.append(next(ch for ch in ALPHA if ch not in ordered_ct))
    while len(eta) < 26:
        eta.append(next(ch for ch in ALPHA if ch not in eta))
    # build mapping cipher->plain index
    m = [0]*26
    for cidx, cch in enumerate(ordered_ct[:26]):
        pch = eta[cidx]
        m[ord(cch)-65] = ord(pch)-65
    # random perturb a bit
    for _ in range(6):
        a,b = random.randrange(26), random.randrange(26)
        m[a],m[b] = m[b],m[a]
    return m

def _mapping_score(ct: str, mapping: list[int]) -> float:
    pt = _substitution_decrypt(ct, mapping)
    return _score_pt(pt)

def solve_substitution(ct: str, time_sec=6.0, restarts=8, start_temp=2.0, end_temp=0.05):
    best_map = None
    best_score = -1e99
    deadline = time.time() + max(0.3, float(time_sec))
    tries = 0
    while time.time() < deadline and tries < max(1,int(restarts)):
        tries += 1
        # initial mapping
        mapping = _freq_init_mapping(ct) if tries % 2 else _random_mapping()
        score = _mapping_score(ct, mapping)
        temp = float(start_temp)
        # SA parameters
        inner_deadline = min(deadline, time.time() + (time_sec / max(1,restarts)))
        while time.time() < inner_deadline and temp > end_temp:
            # try several random swaps per temperature step
            for _ in range(600):
                a,b = random.randrange(26), random.randrange(26)
                if a==b: continue
                mapping[a], mapping[b] = mapping[b], mapping[a]
                new_score = _mapping_score(ct, mapping)
                delta = new_score - score
                if delta >= 0 or random.random() < math.exp(delta/max(1e-6,temp)):
                    score = new_score
                    if score > best_score:
                        best_score = score
                        best_map = mapping[:]
                else:
                    # revert
                    mapping[a], mapping[b] = mapping[b], mapping[a]
            temp *= 0.88
    if best_map is None:
        best_map = _freq_init_mapping(ct)
        best_score = _mapping_score(ct, best_map)
    return best_map, best_score, _substitution_decrypt(ct, best_map)
# --- FIX: BaseGuesser + candidate plumbing + GUI bridge ----------------------
# Put this ABOVE any "class ...Guesser(BaseGuesser)" definitions.

# Base class for all guessers
if 'BaseGuesser' not in globals():
    class BaseGuesser:
        """Minimal abstract base for guessers used by Smart Guess/Brute Force."""
        name = "Base"
        def generate(self, ct: str, budget: int = 0):
            raise NotImplementedError

# Helper used by some guessers (alias to an alpha-only upper cleaner)
if '_clean_alpha' not in globals():
    def _clean_alpha(s: str) -> str:
        return "".join(ch for ch in s.upper() if 'A' <= ch <= 'Z')

# Shared candidate buffer + helpers (higher score = better; uses _score_pt)
_CAND_POOL = []

def begin_candidates():
    """Start a new candidate-collection session."""
    _CAND_POOL.clear()

def push_candidate(family: str, key: str, plaintext: str, score: float, meta: dict | None = None):
    """Append a candidate produced by any guesser."""
    try:
        sc = float(score)
    except Exception:
        sc = -1e99
    _CAND_POOL.append({
        "family": family,
        "key": key or "",
        "plaintext": plaintext or "",
        "score": sc,
        "meta": meta or {}
    })

def get_ranked_candidates(limit: int = 50):
    """Return de-duplicated candidates ranked by score (desc)."""
    best = {}
    for row in _CAND_POOL:
        pt = row["plaintext"]
        sc = row["score"]
        if pt not in best or sc > best[pt]["score"]:
            best[pt] = row
    ranked = sorted(best.values(), key=lambda r: r["score"], reverse=True)
    return [(f'{r["family"]} [{r["key"]}]', r["plaintext"], r["score"]) for r in ranked[:limit]]

# Registry + registration helpers for guessers (optional, convenient)
_GUESSERS = []
def register_guesser(cls):
    """Decorator to auto-register a guesser class."""
    try:
        _GUESSERS.append(cls())
    except Exception:
        pass
    return cls

def _try_register_existing(names: list[str]):
    for n in names:
        cls = globals().get(n)
        if isinstance(cls, type):
            try:
                _GUESSERS.append(cls())
            except Exception:
                pass

# GUI bridge: make Smart Guess run BOTH the legacy SmartGuess() and any new guessers
def _smart_guess_with_guessers(self):
    ct = self.input_txt.get("1.0", "end-1c")

    # 1) New-style guessers fill the shared pool
    begin_candidates()
    for g in _GUESSERS:
        try:
            g.generate(ct)
        except Exception:
            # Keep going; one bad guesser shouldn't kill the run
            pass

    # 2) Merge in results from the legacy SmartGuess() by rescoring with _score_pt
    try:
        legacy = SmartGuess(ct)  # returns (label, pt, legacy_score) with "lower is better"
        for label, pt, _legacy_sc in legacy:
            try:
                sc = _score_pt(pt)  # convert to our "higher is better" space
            except Exception:
                sc = 0.0
            push_candidate("Legacy " + label, "", pt, sc)
    except Exception:
        pass

    ranked = get_ranked_candidates(limit=50)
    self._show_ranked_window("Smart Guess — Unified Candidates", ranked)

# Install the GUI bridge once CipherGUI exists
def _install_gui_bridge_for_guessers():
    if 'CipherGUI' not in globals():
        return
    if not hasattr(CipherGUI, "_smart_guess_legacy"):
        CipherGUI._smart_guess_legacy = CipherGUI.smart_guess
        CipherGUI.smart_guess = _smart_guess_with_guessers

_install_gui_bridge_for_guessers()
# --- end fix block -----------------------------------------------------------

class SubstitutionGuesser(BaseGuesser):
    name = "Substitution"
    def generate(self, ct, budget=1):
        if not GUESSER_OPTIONS["Substitution"].get("enabled", True):
            return
        t  = float(GUESSER_OPTIONS["Substitution"].get("time_sec", 6.0))
        rs = int(GUESSER_OPTIONS["Substitution"].get("restarts", 8))
        t0 = float(GUESSER_OPTIONS["Substitution"].get("start_temp", 2.0))
        t1 = float(GUESSER_OPTIONS["Substitution"].get("end_temp", 0.05))
        m, sc, pt = solve_substitution(ct, time_sec=t, restarts=rs, start_temp=t0, end_temp=t1)
        key = "".join(ALPHA[i] for i in m)  # mapping row (C->P indexes as letters)
        push_candidate("Substitution", key, pt, sc, {"time":t,"restarts":rs})

# =============================================================================
# EXTRA GUESSERS: ROT13 / ROT47 / Playfair (seeded) / ADFGX / ADFGVX
# =============================================================================

# ROT13 / ROT47
def rot13_dec(s: str) -> str:
    out=[]
    for ch in s:
        if 'A' <= ch <= 'Z':
            out.append(chr((ord(ch)-65-13)%26+65))
        elif 'a' <= ch <= 'z':
            out.append(chr((ord(ch)-97-13)%26+97))
        else:
            out.append(ch)
    return "".join(out)

def rot47_dec(s: str) -> str:
    out=[]
    for ch in s:
        o = ord(ch)
        if 33 <= o <= 126:
            out.append(chr(33 + ((o - 33 - 47) % 94)))
        else:
            out.append(ch)
    return "".join(out)

class ROT13Guesser(BaseGuesser):
    name = "ROT13"
    def generate(self, ct, budget=1):
        if not GUESSER_OPTIONS["ROT13"].get("enabled", True):
            return
        pt = rot13_dec(ct)
        sc = _score_pt(pt)
        push_candidate("ROT13", "rot13", pt, sc)

class ROT47Guesser(BaseGuesser):
    name = "ROT47"
    def generate(self, ct, budget=1):
        if not GUESSER_OPTIONS["ROT47"].get("enabled", True):
            return
        pt = rot47_dec(ct)
        sc = _score_pt(pt)
        push_candidate("ROT47", "rot47", pt, sc)

# --- Playfair helpers --------------------------------------------------------
def playfair_square_from_keyword(keyword: str):
    key = _clean_alpha(keyword).replace("J","I")
    seen=set(); letters=[]
    for ch in key + ALPHA:
        if ch=="J": ch="I"
        if ch not in seen and ch in ALPHA and ch!="J":
            seen.add(ch); letters.append(ch)
        if len(letters)==25: break
    table = [letters[i*5:(i+1)*5] for i in range(5)]
    pos = {}
    for r in range(5):
        for c in range(5):
            pos[table[r][c]] = (r,c)
    return table, pos

def playfair_dec(ct: str, keyword: str) -> str:
    table, pos = playfair_square_from_keyword(keyword)
    def pf(c1,c2):
        r1,c1 = pos[c1]; r2,c2 = pos[c2]
        if r1 == r2:
            return table[r1][(c1-1)%5] + table[r2][(c2-1)%5]
        elif c1 == c2:
            return table[(r1-1)%5][c1] + table[(r2-1)%5][c2]
        else:
            return table[r1][c2] + table[r2][c1]
    # build digraphs from letters only, pairing as-is (ignore X insert nuance)
    s = _clean_alpha(ct)
    if len(s)%2==1: s += "X"
    out=[]
    for i in range(0,len(s),2):
        a,b = s[i], s[i+1]
        # merge Js to I
        a = "I" if a=="J" else a
        b = "I" if b=="J" else b
        out.append(pf(a,b))
    pt_alpha = "".join(out)
    # map back over original text preserving non-alpha and case
    res=[]; j=0
    for ch in ct:
        if ch.upper() in ALPHA:
            pc = pt_alpha[j]
            res.append(pc if ch.isupper() else pc.lower())
            j+=1
        else:
            res.append(ch)
    return "".join(res)

class PlayfairGuesser(BaseGuesser):
    name = "Playfair"
    def generate(self, ct, budget=80):
        if not GUESSER_OPTIONS["Playfair"].get("enabled", True):
            return
        # Try a small bank of seed keywords
        seeds = GUESSER_OPTIONS["Playfair"].get("seed_words","KEYWORD,SECRET,MONARCHY").split(",")
        seeds = [w.strip() for w in seeds if w.strip()]
        tried=set()
        for w in seeds[:16]:
            try:
                pt = playfair_dec(ct, w)
                sc = _score_pt(pt)
                push_candidate("Playfair", w, pt, sc)
                tried.add(w)
            except Exception:
                pass
        # Mutate seeds a bit by appending frequent letters - quick variants
        eta = "ETAOINSHRDLU"
        max_var = int(GUESSER_OPTIONS["Playfair"].get("max_variants", 8))
        for w in list(tried):
            for ch in eta[:6]:
                if len(tried) >= max_var + len(seeds): break
                k = w + ch
                try:
                    pt = playfair_dec(ct, k)
                    sc = _score_pt(pt)
                    push_candidate("Playfair", k, pt, sc)
                    tried.add(k)
                except Exception:
                    pass

# --- ADFGX / ADFGVX helpers --------------------------------------------------
ADFG = "ADFGX"
ADFGV = "ADFGVX"

def keyed_square_5x5(keyword: str):
    key = _clean_alpha(keyword).replace("J","I")
    seq=[]
    seen=set()
    for ch in key + ALPHA:
        if ch=="J": ch="I"
        if ch not in seen and ch!="J":
            seen.add(ch); seq.append(ch)
        if len(seq)==25: break
    return seq  # flat list

def keyed_square_6x6(keyword: str):
    alpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    key = "".join(ch for ch in _clean_alpha(keyword) if ch in ALPHA)
    seq=[]; seen=set()
    for ch in key + alpha:
        if ch not in seen:
            seen.add(ch); seq.append(ch)
        if len(seq)==36: break
    return seq

def _columnar_unpermute(ct: str, key: str):
    # Inverse of columnar transposition used by ADFGX/ADFGVX (read down columns by key order)
    w = len(key)
    n = len(ct)
    rows = math.ceil(n / w)
    short = (w*rows - n)
    col_len = [rows]*(w-short) + [rows-1]*short

    order = sorted(range(w), key=lambda i: (key[i], i))  # stable for dups
    cols = {}
    idx = 0
    for oi in order:
        L = col_len[oi]
        cols[oi] = list(ct[idx:idx+L]); idx += L
    # rebuild row-wise
    out=[]
    for r in range(rows):
        for c in range(w):
            if r < len(cols[c]):
                out.append(cols[c][r])
    return "".join(out)

def adfgx_dec(ct: str, square_key="KEYWORD", trans_key="CIPHER"):
    # 1) strip to ADFGX letters
    s = "".join(ch for ch in ct.upper() if ch in ADFG)
    if len(s) % 2 != 0:
        s = s[:-1]
    if not s: return ""
    # 2) inverse columnar
    inter = _columnar_unpermute(s, trans_key)
    # 3) map pairs through 5x5 square
    sq = keyed_square_5x5(square_key)
    res=[]
    for i in range(0, len(inter), 2):
        r = ADFG.index(inter[i])
        c = ADFG.index(inter[i+1])
        ch = sq[r*5 + c]
        res.append(ch)
    # 4) case/punct reinsert (simple upper only)
    return "".join(res)

def adfgvx_dec(ct: str, square_key="KEYWORD", trans_key="CIPHER"):
    s = "".join(ch for ch in ct.upper() if ch in ADFGV)
    if len(s) % 2 != 0:
        s = s[:-1]
    if not s: return ""
    inter = _columnar_unpermute(s, trans_key)
    sq = keyed_square_6x6(square_key)
    res=[]
    for i in range(0, len(inter), 2):
        r = ADFGV.index(inter[i])
        c = ADFGV.index(inter[i+1])
        ch = sq[r*6 + c]
        res.append(ch)
    return "".join(res)

class ADFGXGuesser(BaseGuesser):
    name = "ADFGX"
    def generate(self, ct, budget=120):
        if not GUESSER_OPTIONS["ADFGX"].get("enabled", True):
            return
        S = "".join(ch for ch in ct.upper() if ch in ADFG)
        if len(S) < 10:  # likely not ADFGX
            return
        sq_key = GUESSER_OPTIONS["ADFGX"].get("square_key","KEYWORD")
        kmin = int(GUESSER_OPTIONS["ADFGX"].get("min_klen",4))
        kmax = int(GUESSER_OPTIONS["ADFGX"].get("max_klen",8))
        # try numeric keys (abcdef order) – simulate small widths
        for w in range(kmin, kmax+1):
            # try a small set of columnar keys by permuting alphabetically unique keys of len w
            base = "CIPHERKEYALNUMBADFGX"
            key = "".join(dict.fromkeys((base + sq_key + "ABCDEFGHIJKLMNOPQRSTUVWXYZ")) )[:w]
            pt_alpha = adfgx_dec(ct, sq_key, key)
            # score mapping letters as plaintext
            sc = _score_pt(pt_alpha)
            push_candidate("ADFGX", f"square={sq_key} trans={key}", pt_alpha, sc, {"klen":w})

class ADFGVXGuesser(BaseGuesser):
    name = "ADFGVX"
    def generate(self, ct, budget=120):
        if not GUESSER_OPTIONS["ADFGVX"].get("enabled", True):
            return
        S = "".join(ch for ch in ct.upper() if ch in ADFGV)
        if len(S) < 10:
            return
        sq_key = GUESSER_OPTIONS["ADFGVX"].get("square_key","KEYWORD")
        kmin = int(GUESSER_OPTIONS["ADFGVX"].get("min_klen",4))
        kmax = int(GUESSER_OPTIONS["ADFGVX"].get("max_klen",8))
        base = "CIPHERKEYALNUMADFGVX"
        for w in range(kmin, kmax+1):
            key = "".join(dict.fromkeys((base + sq_key + "ABCDEFGHIJKLMNOPQRSTUVWXYZ")) )[:w]
            pt_alpha = adfgvx_dec(ct, sq_key, key)
            sc = _score_pt(pt_alpha)
            push_candidate("ADFGVX", f"square={sq_key} trans={key}", pt_alpha, sc, {"klen":w})

# =============================================================================
# EXTEND GUESSERS REGISTRY + obey per-cipher options (enable, ranges)
# =============================================================================
# Reuse existing decoders from previous patch: caesar_dec, affine_dec, railfence_dec, columnar_dec,
# vigenere_dec, autokey_dec, beaufort_dec, porta_dec

# Rebuild/extend registry to include new guessers and option-gated ranges
class RailFenceGuesser(BaseGuesser):
    name = "Rail Fence"
    def generate(self, ct, budget=24):
        opts = GUESSER_OPTIONS["Rail Fence"]
        if not opts.get("enabled", True): return
        lo = max(2, int(opts.get("min_rails", 2)))
        hi = min(24, int(opts.get("max_rails", 12)))
        for rails in range(lo, hi+1):
            pt = railfence_dec(ct, rails)
            sc = _score_pt(pt)
            push_candidate("Rail Fence", f"rails={rails}", pt, sc)

class ColumnarGuesser(BaseGuesser):
    name = "Columnar"
    def generate(self, ct, budget=40):
        opts = GUESSER_OPTIONS["Columnar"]
        if not opts.get("enabled", True): return
        lo = max(2, int(opts.get("min_width",2)))
        hi = min(28, int(opts.get("max_width",14)))
        n = len(ct)
        for w in range(lo, min(hi, max(2, int(math.sqrt(max(1,n)))+8))+1):
            pt = columnar_dec(ct, w)
            sc = _score_pt(pt)
            push_candidate("Columnar", f"width={w}", pt, sc)

class VigenereGuesser(BaseGuesser):
    name = "Vigenere"
    def generate(self, ct, budget=200):
        opts = GUESSER_OPTIONS["Vigenere"]
        if not opts.get("enabled", True): return
        max_len = int(opts.get("max_len",16))
        topk    = int(opts.get("top_keys_per_len",3))
        lens = suggest_vigenere_key_lengths(ct, max_len=max_len)
        for m in lens[:8]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=topk)
            for k in keys:
                pt = vigenere_dec(ct, k)
                sc = _score_pt(pt)
                push_candidate("Vigenere", k, pt, sc, {"len":m})

class AutokeyGuesser(BaseGuesser):
    name = "Autokey"
    def generate(self, ct, budget=80):
        opts = GUESSER_OPTIONS["Autokey"]
        if not opts.get("enabled", True): return
        max_len = int(opts.get("max_len",12))
        lens = suggest_vigenere_key_lengths(ct, max_len=max_len)
        for m in lens[:6]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=int(opts.get("seed_try",2)))
            for k in keys:
                seed = k[:max(3, min(6, len(k)))]
                pt = autokey_dec(ct, seed)
                sc = _score_pt(pt)
                push_candidate("Autokey", seed, pt, sc, {"seed_len":len(seed)})

class BeaufortGuesser(BaseGuesser):
    name = "Beaufort"
    def generate(self, ct, budget=120):
        opts = GUESSER_OPTIONS["Beaufort"]
        if not opts.get("enabled", True): return
        max_len = int(opts.get("max_len",14))
        lens = suggest_vigenere_key_lengths(ct, max_len=max_len)
        for m in lens[:6]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=2)
            for k in keys:
                pt = beaufort_dec(ct, k)
                sc = _score_pt(pt)
                push_candidate("Beaufort", k, pt, sc)

class PortaGuesser(BaseGuesser):
    name = "Porta"
    def generate(self, ct, budget=80):
        opts = GUESSER_OPTIONS["Porta"]
        if not opts.get("enabled", True): return
        max_len = int(opts.get("max_len",14))
        lens = suggest_vigenere_key_lengths(ct, max_len=max_len)
        for m in lens[:6]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=2)
            for k in keys:
                pt = porta_dec(ct, k)
                sc = _score_pt(pt)
                push_candidate("Porta", k, pt, sc)

class CaesarGuesser(BaseGuesser):
    name = "Caesar/ROT"
    def generate(self, ct, budget=40):
        if not GUESSER_OPTIONS["Caesar"].get("enabled", True): return
        for sh in range(26):
            pt = caesar_dec(ct, sh)
            sc = _score_pt(pt)
            push_candidate("Caesar", f"shift={sh}", pt, sc)

class AffineGuesser(BaseGuesser):
    name = "Affine"
    def generate(self, ct, budget=312):
        if not GUESSER_OPTIONS["Affine"].get("enabled", True): return
        m = 26
        for a in [x for x in range(1,m) if math.gcd(x,m)==1]:
            for b in range(m):
                pt = affine_dec(ct, a, b)
                sc = _score_pt(pt)
                push_candidate("Affine", f"a={a}, b={b}", pt, sc)

# Re-register guessers (preserving earlier ones but replacing with option-aware)
_GUESSERS = [
    CaesarGuesser(),
    ROT13Guesser(),
    ROT47Guesser(),
    AffineGuesser(),
    RailFenceGuesser(),
    ColumnarGuesser(),
    VigenereGuesser(),
    AutokeyGuesser(),
    BeaufortGuesser(),
    PortaGuesser(),
    PlayfairGuesser(),
    ADFGXGuesser(),
    ADFGVXGuesser(),
    SubstitutionGuesser(),
]

# =============================================================================
# Glue: make sure Smart Guess / Brute Force already wrapped collect candidates
# (previous block installed wrappers and candidates panel + CSV export)
# =============================================================================

# Nothing else to wire here; GUESSERS list is consumed by run_all_guessers().

# =============================================================================
# Optional: Add a toolbar row with quick preset buttons (nice QoL)
# =============================================================================
def _add_presets_toolbar(self):
    try:
        # place under existing toolbar/status if available
        container = ttk.Frame(self.left_pane)
        container.pack(fill="x", padx=8, pady=(0,6))
        ttk.Label(container, text="Scoring Presets:", font=("TkDefaultFont", 9)).pack(side="left")
        for name in ["Balanced","Quadgram-heavy","Fast (chi² only)"]:
            ttk.Button(container, text=name, command=lambda n=name: (apply_scoring_preset(n), messagebox.showinfo("Presets", f"Applied: {n}"))).pack(side="left", padx=4)
    except Exception:
        pass

def install_presets_toolbar():
    if 'CipherGUI' not in globals():
        return
    if not hasattr(CipherGUI, "_post_layout_original_presets"):
        old = getattr(CipherGUI, "_post_layout", lambda self: None)
        def _post_layout_wrap(self):
            try: old(self)
            except Exception: pass
            _add_presets_toolbar(self)
        CipherGUI._post_layout = _post_layout_wrap

install_presets_toolbar()

import time
import itertools
import json
import tkinter as tk
from tkinter import ttk, messagebox
try:
    from tkinter import filedialog as fd
except Exception:
    fd = None

# --- Matplotlib for heatmaps -------------------------------------------------
try:
    import matplotlib
    matplotlib.use("Agg")
    from matplotlib.figure import Figure
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    _HAS_MPL = True
except Exception:
    _HAS_MPL = False

ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

# -----------------------------------------------------------------------------
# Utility: normalization / sanitization
# -----------------------------------------------------------------------------
def _clean_alpha(s: str, keep_spaces=False):
    out = []
    for ch in s:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            out.append(u)
        elif keep_spaces and ch.isspace():
            out.append(' ')
    return "".join(out)

def _modinv(a, m):
    # Modular inverse for Affine
    a = a % m
    for x in range(1, m):
        if (a * x) % m == 1:
            return x
    raise ValueError("No modular inverse")

def _shift_char(c, k):
    return ALPHA[(ALPHA.index(c)+k) % 26]

def _deshift_char(c, k):
    return ALPHA[(ALPHA.index(c)-k) % 26]



# -----------------------------------------------------------------------------
# Candidate collection (used by patched SmartGuess/BruteForce + our engines)
# -----------------------------------------------------------------------------
class Candidate:
    __slots__ = ("cipher","key","plaintext","score","extra")
    def __init__(self, cipher, key, plaintext, score, extra=None):
        self.cipher = cipher
        self.key = key
        self.plaintext = plaintext
        self.score = float(score)
        self.extra = extra or {}
    def as_row(self):
        return {
            "cipher": self.cipher,
            "key": self.key,
            "score": f"{self.score:.6f}",
            "plaintext": self.plaintext,
            **{f"meta_{k}":v for k,v in self.extra.items()}
        }

class ResultCollector:
    def __init__(self):
        self._items = []
        self._start_ts = time.time()
    def clear(self):
        self._items.clear()
        self._start_ts = time.time()
    def push(self, cand: Candidate):
        self._items.append(cand)
    def items(self):
        return list(self._items)
    def best(self, n=1):
        return sorted(self._items, key=lambda c: c.score, reverse=True)[:n]
    def export_csv(self, path):
        import csv
        rows = [c.as_row() for c in self.best(99999)]
        if not rows:
            rows = [{"cipher":"","key":"","score":"","plaintext":""}]
        fieldnames = list(rows[0].keys())
        with open(path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            for r in rows:
                w.writerow(r)

# We keep one global collector and attach to GUI instances.
_GLOBAL_COLLECTOR = ResultCollector()

def clear_candidates():
    _GLOBAL_COLLECTOR.clear()

def push_candidate(cipher, key, plaintext, score, extra=None):
    _GLOBAL_COLLECTOR.push(Candidate(cipher, key, plaintext, score, extra))

# Expose to other parts of the codebase if needed
globals()['CANDIDATE_COLLECTOR'] = _GLOBAL_COLLECTOR
globals()['push_candidate'] = push_candidate
globals()['clear_candidates'] = clear_candidates

# -----------------------------------------------------------------------------
# Decoders (light, independent fallbacks for our guessers)
# -----------------------------------------------------------------------------
def caesar_dec(ct: str, shift: int) -> str:
    s = []
    for ch in ct:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            base = ord('A') if ch.isupper() else ord('a')
            s.append(chr((ord(ch)-base - shift) % 26 + base))
        else:
            s.append(ch)
    return "".join(s)

def affine_dec(ct: str, a: int, b: int) -> str:
    # y = a*x + b mod 26
    inv = _modinv(a, 26)
    out = []
    for ch in ct:
        if ch.upper() in ALPHA:
            alpha = ALPHA if ch.isupper() else ALPHA.lower()
            y = alpha.index(ch)
            x = (inv * (y - b)) % 26
            out.append(alpha[x])
        else:
            out.append(ch)
    return "".join(out)

def vigenere_dec(ct: str, key: str) -> str:
    key = _clean_alpha(key)
    if not key: return ct
    out = []
    ki = 0
    for ch in ct:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            shift = ALPHA.index(key[ki % len(key)])
            base = ord('A') if ch.isupper() else ord('a')
            out.append(chr((ord(ch)-base - shift) % 26 + base))
            ki += 1
        else:
            out.append(ch)
    return "".join(out)

def autokey_dec(ct: str, key: str) -> str:
    # Vigenère where key extends with plaintext
    key = _clean_alpha(key)
    out = []
    kbuf = list(key)
    for ch in ct:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            shift = ALPHA.index(kbuf[0]) if kbuf else 0
            base = ord('A') if ch.isupper() else ord('a')
            p = chr((ord(ch)-base - shift) % 26 + base)
            out.append(p)
            # extend with plaintext letter upper
            kbuf.append(p.upper())
            kbuf.pop(0) if len(kbuf) > len(key) else None
        else:
            out.append(ch)
    return "".join(out)

def beaufort_dec(ct: str, key: str) -> str:
    # P = K - C mod 26, with Vigenère-like stepping
    key = _clean_alpha(key)
    out = []
    ki = 0
    for ch in ct:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            kc = key[ki % len(key)]
            p_idx = (ALPHA.index(kc) - ALPHA.index(u)) % 26
            out.append(ALPHA[p_idx] if ch.isupper() else ALPHA[p_idx].lower())
            ki += 1
        else:
            out.append(ch)
    return "".join(out)

def porta_dec(ct: str, key: str) -> str:
    # Porta is reciprocal; implement classic digraph table as shifts of 13.. etc.
    key = _clean_alpha(key)
    def porta_map(kch):
        i = ALPHA.index(kch)//2  # A/B -> 0, C/D -> 1, ...
        left  = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        right = "NOPQRSTUVWXYZABCDEFGHIJKLM"
        # rotate halves by i
        L = left[:13]; R = right[:13]
        Lr = L[i:]+L[:i]
        Rr = R[i:]+R[:i]
        table = {}
        for a,b in zip(Lr, Rr):
            table[a]=b; table[b]=a
        return table
    out=[]; ki=0
    for ch in ct:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            t = porta_map(key[ki % len(key)])
            m = t.get(u,u)
            out.append(m if ch.isupper() else m.lower())
            ki+=1
        else:
            out.append(ch)
    return "".join(out)

def railfence_dec(ct: str, rails: int) -> str:
    # Reconstruct zig-zag indices, then assign chars row-wise
    if rails <= 1: return ct
    n = len(ct)
    # pattern of rows visited
    pattern = list(range(rails)) + list(range(rails-2,0,-1))
    rows = [[] for _ in range(rails)]
    # count each row's length
    counts = [0]*rails
    r = 0
    for i in range(n):
        counts[pattern[r]] += 1
        r = (r+1) % len(pattern)
    # fill rows from ciphertext
    idx = 0
    for ri in range(rails):
        rows[ri] = list(ct[idx:idx+counts[ri]])
        idx += counts[ri]
    # read off zig-zag
    out=[]
    rptr = [0]*rails
    r=0
    for i in range(n):
        row = pattern[r]
        out.append(rows[row][rptr[row]])
        rptr[row]+=1
        r = (r+1) % len(pattern)
    return "".join(out)

def columnar_dec(ct: str, width: int, keyperm=None) -> str:
    # Simple columnar: fill columns top->bottom using key order; then read rows
    c = list(ct)
    n = len(c)
    w = max(1, width)
    rows = math.ceil(n / w)
    # determine column lengths (last row may be short)
    short = (w*rows - n)
    col_len = [rows]*(w-short) + [rows-1]*short
    # order of columns (if permutation not given, use numeric ascending)
    if keyperm is None:
        order = list(range(w))
    else:
        order = list(keyperm)
        if len(order)!=w: order = list(range(w))
    # slice ct into columns by order
    cols = [None]*w
    idx=0
    for k in order:
        L = col_len[k]
        cols[k] = c[idx:idx+L]
        idx += L
    # read row-wise
    out=[]
    for r in range(rows):
        for k in range(w):
            if r < len(cols[k]):
                out.append(cols[k][r])
    return "".join(out)

# -----------------------------------------------------------------------------
# Key length + key letter guessers (Vigenère family)
# -----------------------------------------------------------------------------
def _chi2_for_shift(coset: str, shift: int) -> float:
    # Shift coset backwards (decipher) then chi-squared
    pt = "".join(_deshift_char(c, shift) for c in coset)
    # chi-squared vs English
    freq = Counter(pt)
    N = len(pt) or 1
    expected = {
        'E': 12.702, 'T': 9.056, 'A': 8.167, 'O': 7.507, 'I': 6.966, 'N': 6.749,
        'S': 6.327, 'H': 6.094, 'R': 5.987, 'D': 4.253, 'L': 4.025, 'C': 2.782,
        'U': 2.758, 'M': 2.406, 'W': 2.360, 'F': 2.228, 'G': 2.015, 'Y': 1.974,
        'P': 1.929, 'B': 1.492, 'V': 0.978, 'K': 0.772, 'J': 0.153, 'X': 0.150,
        'Q': 0.095, 'Z': 0.074
    }
    chi = 0.0
    for ch in ALPHA:
        o = freq.get(ch,0) * 100.0 / N
        e = expected[ch]
        if e > 0:
            diff = o - e
            chi += (diff*diff)/e
    return chi

def guess_vigenere_key_by_len(ct: str, m: int, top_k: int = 3) -> list[str]:
    s = _clean_alpha(ct)
    cosets = split_cosets(s, m)
    # best shift per coset (min chi2)
    shifts = []
    for cos in cosets:
        if not cos:
            shifts.append(0); continue
        best = min(range(26), key=lambda sh: _chi2_for_shift(cos, sh))
        shifts.append(best)
    # produce a few alternates by allowing each coset to consider 2nd-best
    # compute per-coset ranked shifts
    ranked = []
    for cos in cosets:
        rnk = sorted(range(26), key=lambda sh: _chi2_for_shift(cos, sh))[:2]
        ranked.append(rnk)
    keys = set()
    for alt in itertools.product(*ranked):
        k = "".join(ALPHA[a] for a in alt)
        keys.add(k)
        if len(keys) >= top_k: break
    # ensure baseline
    if len(keys) < top_k:
        k0 = "".join(ALPHA[s] for s in shifts)
        keys.add(k0)
    return list(keys)[:top_k]

def suggest_vigenere_key_lengths(ct: str, max_len: int = 16) -> list[int]:
    # combine kasiski factor votes + friedman closeness
    _, fac = kasiski_examination(ct, 3, 5, max_len)
    fr = friedman_by_keylen(ct, max_len)
    # score lens: high votes + being close to 0.065
    votes = {k:v for k,v in fac.items()}
    lens = {}
    for m, ic in fr:
        lens[m] = lens.get(m, 0.0) + (max(0, 0.065 - abs(0.065-ic)) * 1000)
    for k,v in votes.items():
        lens[k] = lens.get(k, 0.0) + v * 50.0
    # rank
    ranked = sorted(lens.items(), key=lambda t: t[1], reverse=True)
    return [m for m,_ in ranked][:8]

# -----------------------------------------------------------------------------
# Guessers registry
# -----------------------------------------------------------------------------
class BaseGuesser:
    name = "Base"
    def generate(self, ct: str, budget: int = 200):
        return []  # yield Candidate

class CaesarGuesser(BaseGuesser):
    name = "Caesar/ROT"
    def generate(self, ct, budget=40):
        for sh in range(26):
            pt = caesar_dec(ct, sh)
            sc = _score_pt(pt)
            push_candidate("Caesar", f"shift={sh}", pt, sc)

class AffineGuesser(BaseGuesser):
    name = "Affine"
    def generate(self, ct, budget=312):
        m = 26
        for a in [x for x in range(1,m) if math.gcd(x,m)==1]:
            for b in range(m):
                pt = affine_dec(ct, a, b)
                sc = _score_pt(pt)
                push_candidate("Affine", f"a={a}, b={b}", pt, sc)

class RailFenceGuesser(BaseGuesser):
    name = "Rail Fence"
    def generate(self, ct, budget=24):
        n = len(ct)
        for rails in range(2, min(12, n//2+1)):
            pt = railfence_dec(ct, rails)
            sc = _score_pt(pt)
            push_candidate("Rail Fence", f"rails={rails}", pt, sc)

class ColumnarGuesser(BaseGuesser):
    name = "Columnar"
    def generate(self, ct, budget=40):
        n = len(ct)
        for w in range(2, min(14, max(3, int(math.sqrt(max(1,n)))) + 6)):
            pt = columnar_dec(ct, w)
            sc = _score_pt(pt)
            push_candidate("Columnar", f"width={w}", pt, sc)

class VigenereGuesser(BaseGuesser):
    name = "Vigenere"
    def generate(self, ct, budget=200):
        # lengths from suggestion, capped by budget
        lens = suggest_vigenere_key_lengths(ct, max_len=16)
        for m in lens[:8]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=3)
            for k in keys:
                pt = vigenere_dec(ct, k)
                sc = _score_pt(pt)
                push_candidate("Vigenere", k, pt, sc, {"len":m})

class AutokeyGuesser(BaseGuesser):
    name = "Autokey"
    def generate(self, ct, budget=80):
        lens = suggest_vigenere_key_lengths(ct, max_len=12)
        # try initial seeds derived from Vigenère key guesses (first 3-6 chars)
        for m in lens[:6]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=2)
            for k in keys:
                seed = k[:max(3, min(6, len(k)))]
                pt = autokey_dec(ct, seed)
                sc = _score_pt(pt)
                push_candidate("Autokey", seed, pt, sc, {"seed_len":len(seed)})

class BeaufortGuesser(BaseGuesser):
    name = "Beaufort"
    def generate(self, ct, budget=120):
        lens = suggest_vigenere_key_lengths(ct, max_len=14)
        for m in lens[:6]:
            keys = guess_vigenere_key_by_len(ct, m, top_k=2)
            for k in keys:
                pt = beaufort_dec(ct, k)
                sc = _score_pt(pt)
                push_candidate("Beaufort", k, pt, sc)

class PortaGuesser(BaseGuesser):
    name = "Porta"
    def generate(self, ct, budget=80):
        lens = suggest_vigenere_key_lengths(ct, max_len=14)
        for m in lens[:6]:
            # for Porta, key letters taken but algorithm is reciprocal
            keys = guess_vigenere_key_by_len(ct, m, top_k=2)
            for k in keys:
                pt = porta_dec(ct, k)
                sc = _score_pt(pt)
                push_candidate("Porta", k, pt, sc)

_GUESSERS = [
    CaesarGuesser(),
    AffineGuesser(),
    RailFenceGuesser(),
    ColumnarGuesser(),
    VigenereGuesser(),
    AutokeyGuesser(),
    BeaufortGuesser(),
    PortaGuesser(),
]

def run_all_guessers(ct: str, max_time_sec: float = 3.5, limit_per=9999):
    clear_candidates()
    t0 = time.time()
    for g in _GUESSERS:
        if time.time()-t0 > max_time_sec:
            break
        try:
            g.generate(ct)
        except Exception as e:
            # don't crash; just log a "meta" record for debugging
            push_candidate("ERROR", g.name, f"[{g.name}] failed: {e}", -1e9)

# -----------------------------------------------------------------------------
# IOC Heatmap GUI
# -----------------------------------------------------------------------------
def _gui_open_ic_heatmap_window(self):
    win = tk.Toplevel(self.root)
    win.title("IOC Heatmap (Key length × Coset)")
    win.geometry("920x680")

    top = ttk.Frame(win); top.pack(fill="x", padx=8, pady=8)
    ttk.Label(top, text="Analyze from:").pack(side="left")
    src = tk.StringVar(value="Input")
    ttk.Radiobutton(top, text="Input", variable=src, value="Input").pack(side="left", padx=6)
    ttk.Radiobutton(top, text="Output", variable=src, value="Output").pack(side="left", padx=6)

    ttk.Label(top, text="Min len").pack(side="left", padx=(12,3))
    vmin = tk.IntVar(value=1)
    ttk.Entry(top, textvariable=vmin, width=4).pack(side="left")
    ttk.Label(top, text="Max len").pack(side="left", padx=(12,3))
    vmax = tk.IntVar(value=16)
    ttk.Entry(top, textvariable=vmax, width=4).pack(side="left")

    runbtn = ttk.Button(top, text="Compute", command=lambda: compute())
    runbtn.pack(side="right")

    # figure
    if not _HAS_MPL:
        ttk.Label(win, text="matplotlib not available. Install it to see the heatmap.").pack(pady=16)
        return

    fig = Figure(figsize=(9.2,5.8))
    ax  = fig.add_subplot(1,1,1)
    canvas = FigureCanvasTkAgg(fig, master=win)
    canvas.get_tk_widget().pack(fill="both", expand=True, padx=8, pady=8)

    info = tk.Text(win, height=6, wrap="word"); info.pack(fill="x", padx=8, pady=(0,8))

    def compute():
        text = self.input_txt.get("1.0","end-1c") if src.get()=="Input" else self.output_txt.get("1.0","end-1c")
        s = _clean_alpha(text)
        mn, mx = max(1, vmin.get()), max(vmin.get(), vmax.get())
        lens = list(range(mn, mx+1))
        heat = []
        best_rows = []
        for m in lens:
            cos = split_cosets(s, m)
            row = [index_of_coincidence(c) if len(c)>=2 else 0.0 for c in cos]
            heat.append(row + [None]*(mx - len(row)))  # pad to max width for imshow
            # record summary per length
            avg_ic = sum(v for v in row if v>0)/max(1,len([v for v in row if v>0]))
            best_rows.append((m, avg_ic))

        data = []
        max_cols = mx
        for r in heat:
            data.append([v if v is not None else 0.0 for v in r + [0.0]*(max_cols - len(r))])

        ax.clear()
        import numpy as np
        arr = np.array(data)
        im = ax.imshow(arr, aspect="auto", interpolation="nearest")
        ax.set_xlabel("Coset index")
        ax.set_ylabel("Key length")
        ax.set_yticks(range(len(lens)))
        ax.set_yticklabels([str(m) for m in lens])
        cb = fig.colorbar(im, ax=ax)
        cb.ax.set_ylabel("IC", rotation=90)
        fig.tight_layout()
        canvas.draw()

        info.delete("1.0","end")
        est = friedman_estimate_keylen(s)
        info.insert("1.0", f"Friedman est len ≈ {est:.2f}\n")
        info.insert("end", "Top lengths by avg IC:\n")
        for m,avg in sorted(best_rows, key=lambda t: t[1], reverse=True)[:10]:
            info.insert("end", f"  m={m:2d}  avgIC={avg:.5f}\n")

    compute()

# -----------------------------------------------------------------------------
# Export CSV + Auto-Suggest integration
# -----------------------------------------------------------------------------
def _export_candidates_csv(self):
    if fd is None:
        messagebox.showerror("Export CSV", "File dialog not available on this system.")
        return
    path = fd.asksaveasfilename(
        title="Export Ranked Candidates to CSV",
        defaultextension=".csv",
        filetypes=[("CSV file","*.csv"),("All files","*.*")]
    )
    if not path: return
    try:
        # Use global collector
        _GLOBAL_COLLECTOR.export_csv(path)
        messagebox.showinfo("Export CSV", f"Saved {len(_GLOBAL_COLLECTOR.items())} candidates.\n{path}")
    except Exception as e:
        messagebox.showerror("Export CSV", f"Failed to export: {e}")

def _apply_suggested_key_to_gui(self, key: str, mode: str = "Vigenere"):
    """
    Best-effort: try to set the cipher type and key field in the host GUI.
    We try several attribute conventions; fall back to clipboard + notice.
    """
    ok = False
    try:
        # cipher selection
        for attr in ("set_cipher","select_cipher","choose_cipher"):
            if hasattr(self, attr):
                getattr(self, attr)(mode)
                ok = True
                break
        # sometimes there's a tk variable
        if not ok and hasattr(self, "cipher_var"):
            try:
                self.cipher_var.set(mode); ok = True
            except Exception:
                pass
    except Exception:
        pass

    k_ok = False
    for attr in ("set_key","setKey","apply_key"):
        if hasattr(self, attr):
            try:
                getattr(self, attr)(key); k_ok = True; break
            except Exception:
                pass
    # common tk variable / entry field
    if not k_ok:
        if hasattr(self, "key_var"):
            try: self.key_var.set(key); k_ok=True
            except Exception: pass
        if hasattr(self, "key_entry"):
            try:
                self.key_entry.delete(0,"end")
                self.key_entry.insert(0,key)
                k_ok=True
            except Exception:
                pass

    if not (ok and k_ok):
        # fallback: copy to clipboard and notify
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(key)
        except Exception:
            pass
        messagebox.showinfo("Key Suggested",
            f"Suggested key for {mode}: {key}\n"
            "I copied it to the clipboard. If it didn't auto-fill, paste it into the key box.")

def _autosuggest_buttons_in_kasiski(self, parent_frame):
    # Adds buttons into the existing Kasiski window footer (call from window code)
    # Not strictly required if we patch the Kasiski window creation below.
    pass  # we integrate in window construction patch

# Patch Kasiski window to include an "Auto-Suggest → Vigenère/Autokey" row
def _gui_open_kasiski_window_aug(self):
    # call the original window first (creates widgets we can extend)
    self.__class__.open_kasiski_window_original(self)
    # last created toplevel is the active one; scan for it
    try:
        win = self.root.winfo_children()[-1]
    except Exception:
        return
    # Find a place to add buttons (bottom)
    btnbar = ttk.Frame(win); btnbar.pack(fill="x", padx=8, pady=(0,8))
    ttk.Label(btnbar, text="Auto-Suggest Key Length →").pack(side="left")
    ttk.Button(btnbar, text="Vigenère", command=lambda: _do_autosuggest(self, "Vigenere")).pack(side="left", padx=6)
    ttk.Button(btnbar, text="Autokey", command=lambda: _do_autosuggest(self, "Autokey")).pack(side="left", padx=6)

def _do_autosuggest(self, mode="Vigenere"):
    # Read current source text (input by default)
    try:
        text = self.input_txt.get("1.0","end-1c")
    except Exception:
        text = ""
    # Suggest lengths, pick best, then build best key
    lens = suggest_vigenere_key_lengths(text, max_len=16)
    if not lens:
        messagebox.showwarning("Auto-Suggest", "No viable key lengths found.")
        return
    m = lens[0]
    keys = guess_vigenere_key_by_len(text, m, top_k=1)
    if not keys:
        messagebox.showwarning("Auto-Suggest", f"Unable to derive key for length {m}.")
        return
    key = keys[0]
    _apply_suggested_key_to_gui(self, key, "Vigenere" if mode=="Vigenere" else "Autokey")

# -----------------------------------------------------------------------------
# Smart Guess / Brute Force wrappers: run host + universal guessers + capture
# -----------------------------------------------------------------------------
def _wrap_smart_guess_collect(self):
    # 1) Clear collector
    clear_candidates()

    # 2) Call the host Smart Guess (if present)
    res = None
    try:
        res = self.__class__.smart_guess_original(self)
        # If host returns a ranked list, capture it.
        if isinstance(res, (list, tuple)):
            for item in res:
                try:
                    cipher = item.get("cipher") if isinstance(item, dict) else getattr(item, "cipher", "unknown")
                    key = item.get("key") if isinstance(item, dict) else getattr(item, "key", "")
                    pt = item.get("pt") if isinstance(item, dict) else getattr(item, "plaintext", "")
                    sc = item.get("score") if isinstance(item, dict) else getattr(item, "score", _score_pt(pt))
                    push_candidate(cipher or "Host", key, pt, sc, {"src":"host"})
                except Exception:
                    pass
    except Exception:
        # Don't block on host errors
        pass

    # 3) Run our universal guessers on the INPUT text (raw)
    try:
        text = self.input_txt.get("1.0","end-1c")
    except Exception:
        text = ""
    run_all_guessers(text, max_time_sec=4.0)

    # 4) Keep a ranked list on the GUI instance
    ranked = sorted(_GLOBAL_COLLECTOR.items(), key=lambda c: c.score, reverse=True)
    self._last_ranked_candidates = ranked

    # 5) If we have a best candidate, preview it in output (non-destructive)
    if ranked:
        top = ranked[0]
        try:
            self.output_preview_txt.delete("1.0","end")
            self.output_preview_txt.insert("1.0", f"[{top.cipher}] key={top.key}\n\n{top.plaintext}")
        except Exception:
            # Fallback: replace main output (comment if undesired)
            try:
                self.output_txt.delete("1.0","end")
                self.output_txt.insert("1.0", top.plaintext)
            except Exception:
                pass
    return res

def _wrap_bruteforce_collect(self):
    clear_candidates()
    res = None
    try:
        res = self.__class__.brute_force_original(self)
        if isinstance(res, (list, tuple)):
            for item in res:
                try:
                    cipher = item.get("cipher") if isinstance(item, dict) else getattr(item, "cipher", "unknown")
                    key = item.get("key") if isinstance(item, dict) else getattr(item, "key", "")
                    pt = item.get("pt") if isinstance(item, dict) else getattr(item, "plaintext", "")
                    sc = item.get("score") if isinstance(item, dict) else getattr(item, "score", _score_pt(pt))
                    push_candidate(cipher or "Host", key, pt, sc, {"src":"host"})
                except Exception:
                    pass
    except Exception:
        pass

    try:
        text = self.input_txt.get("1.0","end-1c")
    except Exception:
        text = ""
    # For brute force, allow a bit longer
    run_all_guessers(text, max_time_sec=6.0)

    ranked = sorted(_GLOBAL_COLLECTOR.items(), key=lambda c: c.score, reverse=True)
    self._last_ranked_candidates = ranked
    if ranked:
        top = ranked[0]
        try:
            self.output_preview_txt.delete("1.0","end")
            self.output_preview_txt.insert("1.0", f"[{top.cipher}] key={top.key}\n\n{top.plaintext}")
        except Exception:
            try:
                self.output_txt.delete("1.0","end")
                self.output_txt.insert("1.0", top.plaintext)
            except Exception:
                pass
    return res

# -----------------------------------------------------------------------------
# GUI wiring: add menu items + hotkeys; patch methods
# -----------------------------------------------------------------------------
def _patch_tools_menu_more(self):
    try:
        m = self.root.nametowidget(self.root['menu'])
    except Exception:
        return
    # find or add Tools menu
    # We re-add only once (idempotent-ish)
    # Append extra entries:
    tools = tk.Menu(m, tearoff=0)
    tools.add_command(label="IOC Heatmap… (Ctrl+I)", command=self.open_ic_heatmap_window)
    tools.add_separator()
    tools.add_command(label="Export Ranked Candidates…", command=self.export_candidates_csv)
    # Attach alongside existing "Tools" (won't duplicate text if already used)
    m.add_cascade(label="Analysis", menu=tools)

def _bind_more_hotkeys(self):
    try:
        self.__class__._bind_keys_original(self)
    except Exception:
        pass
    self.root.bind("<Control-i>", lambda e: self.open_ic_heatmap_window())
    self.root.bind("<Control-I>", lambda e: self.open_ic_heatmap_window())

def install_guessers_and_heatmap():
    if 'CipherGUI' not in globals():
        return
    # IOC Heatmap window
    CipherGUI.open_ic_heatmap_window = _gui_open_ic_heatmap_window
    # Export CSV method
    CipherGUI.export_candidates_csv = _export_candidates_csv

    # If Kasiski window exists, augment with autosuggest buttons by wrapping
    if not hasattr(CipherGUI, "open_kasiski_window_original"):
        CipherGUI.open_kasiski_window_original = CipherGUI.open_kasiski_window
        CipherGUI.open_kasiski_window = _gui_open_kasiski_window_aug

    # Extend menu and bindings (on top of earlier patches)
    if not hasattr(CipherGUI, "_build_menu_original_more"):
        CipherGUI._build_menu_original_more = CipherGUI._build_menu
        CipherGUI._build_menu = lambda self_: (CipherGUI._build_menu_original_more(self_), _patch_tools_menu_more(self_))
    if not hasattr(CipherGUI, "_bind_keys_original_more"):
        CipherGUI._bind_keys_original_more = CipherGUI._bind_keys
        CipherGUI._bind_keys = lambda self_: (CipherGUI._bind_keys_original_more(self_), _bind_more_hotkeys(self_))

    # Wrap smart_guess / brute_force again to collect + add our candidates
    if not hasattr(CipherGUI, "smart_guess_original2"):
        CipherGUI.smart_guess_original2 = CipherGUI.smart_guess
        CipherGUI.smart_guess = _wrap_smart_guess_collect
    if not hasattr(CipherGUI, "brute_force_original2"):
        CipherGUI.brute_force_original2 = CipherGUI.brute_force
        CipherGUI.brute_force = _wrap_bruteforce_collect

install_guessers_and_heatmap()

# =============================================================================
# OPTIONAL: small status panel showing top N candidates live (non-intrusive)
# (If your GUI already has a preview, this is skipped gracefully.)
# =============================================================================
def _attach_candidates_panel(self):
    try:
        container = ttk.Frame(self.right_pane)
    except Exception:
        return
    try:
        container.pack(fill="both", expand=False, padx=8, pady=(4,8))
        ttk.Label(container, text="Top Candidates (live)", font=("TkDefaultFont", 9, "bold")).pack(anchor="w")
        tree = ttk.Treeview(container, columns=("rank","cipher","key","score"), show="headings", height=6)
        for col,w in (("rank",50),("cipher",120),("key",220),("score",100)):
            tree.heading(col, text=col)
            tree.column(col, width=w, anchor="w")
        tree.pack(fill="x", pady=(4,0))
        # attach as attribute
        self._cand_tree = tree
        # periodic updater
        def refresh():
            try:
                items = getattr(self, "_last_ranked_candidates", [])[:12]
                tree.delete(*tree.get_children())
                for i,c in enumerate(items, start=1):
                    tree.insert("", "end", values=(i, c.cipher, c.key, f"{c.score:.3f}"))
            except Exception:
                pass
            finally:
                try:
                    self.root.after(800, refresh)
                except Exception:
                    pass
        refresh()
    except Exception:
        pass

def install_candidates_panel():
    if 'CipherGUI' not in globals():
        return
    if not hasattr(CipherGUI, "_post_layout_original"):
        # Assume CipherGUI has a _post_layout hook after building widgets
        CipherGUI._post_layout_original = getattr(CipherGUI, "_post_layout", lambda self: None)
        def _post_layout_wrap(self):
            try:
                self._post_layout_original()
            except Exception:
                pass
            _attach_candidates_panel(self)
        CipherGUI._post_layout = _post_layout_wrap

install_candidates_panel()
# =============================================================================
# TEST BENCH (tab + window) — roundtrip + known-vector tests, CSV export
# =============================================================================
import time, csv, io, json, math, random
from collections import namedtuple

# ---- utilities ---------------------------------------------------------------
def _exists(fn_name: str) -> bool:
    return fn_name in globals() and callable(globals()[fn_name])

def _try(fn_name: str, default=None):
    try:
        return globals()[fn_name]
    except KeyError:
        return default

def _norm_alpha(s: str) -> str:
    # Normalize text for comparison: A..Z only
    return "".join(ch for ch in s.upper() if 'A' <= ch <= 'Z')

def _norm_words(s: str) -> str:
    # looser normalization: letters + spaces collapsed
    out=[]
    last_space=False
    for ch in s:
        u = ch.upper()
        if 'A' <= u <= 'Z':
            out.append(u); last_space=False
        elif ch.isspace():
            if not last_space:
                out.append(' ')
            last_space=True
    return "".join(out).strip()

def _norm_playfair(s: str) -> str:
    # Allow X padding and I/J conflation
    t = _norm_alpha(s).replace('J','I')
    # Remove probable padding X between duplicate letters or at end — heuristic
    # Keep it simple: just strip trailing X
    return t[:-1] if t.endswith('X') else t

def _ok_eq(a: str, b: str) -> bool:
    return _norm_alpha(a) == _norm_alpha(b)

def _ok_words(a: str, b: str) -> bool:
    return _norm_words(a) == _norm_words(b)

def _safe_call(fn, *args, **kwargs):
    try:
        return True, fn(*args, **kwargs)
    except Exception as e:
        return False, e

# ---- test model --------------------------------------------------------------
TestCase = namedtuple("TestCase",
    "family name mode enc_fn dec_fn params pt ref_ct normalizer")

# mode: "roundtrip" or "decode_only"
# enc_fn/dec_fn: callables or None
# params: dict merged into enc/dec kwargs
# pt: plaintext for roundtrip; ref_ct: known ciphertext for decode_only
# normalizer: one of (_norm_alpha, _norm_words, _norm_playfair) or custom

def _mk_roundtrip(family, name, enc, dec, pt, params=None, norm=None):
    return TestCase(family, name, "roundtrip", enc, dec, params or {}, pt, None, norm or _norm_words)

def _mk_decode_only(family, name, dec, ref_ct, exp_pt, params=None, norm=None):
    # piggy-back 'pt' to carry expected plaintext
    return TestCase(family, name, "decode_only", None, dec, params or {}, exp_pt, ref_ct, norm or _norm_words)

# --- Test Bench primitives (put this above class CipherGUI) -------------------
from dataclasses import dataclass, field
from typing import Callable, Optional, Dict, List

Normalizer = Optional[Callable[[str], str]]

@dataclass
class TestCase:
    cipher: str
    title: str
    enc: Optional[Callable] = None
    dec: Optional[Callable] = None
    params: Dict[str, str] = field(default_factory=dict)
    pt: Optional[str] = None
    ct: Optional[str] = None
    normalizer: Normalizer = None  # <-- default fixes the __new__ error

def _norm_words(s: str) -> str:
    s = "".join(ch if (ch.isalpha() or ch.isspace()) else " " for ch in s.upper())
    return " ".join(s.split())

def _build_tests() -> List[TestCase]:
    T: List[TestCase] = []
    # Simple sanity tests; add more as you like
    pt = "THIS IS A SECRET"
    ct = Caesar_encode(pt, 1, keep_others=True)
    T.append(TestCase(
        cipher="Caesar",
        title="Caesar shift 1",
        enc=Caesar_encode,
        dec=Caesar_decode,
        params={"shift": "1"},
        pt=pt,
        ct=ct,
        normalizer=_norm_words
    ))
    return T

class TestBench(ttk.Frame):
    def __init__(self, master):
        super().__init__(master)
        self.tests = _build_tests()
        self.tree = ttk.Treeview(self, columns=("cipher","title","result"), show="headings")
        self.tree.heading("cipher", text="Cipher"); self.tree.column("cipher", width=140, anchor="w")
        self.tree.heading("title",  text="Title");  self.tree.column("title",  width=260, anchor="w")
        self.tree.heading("result", text="Result"); self.tree.column("result", width=140, anchor="w")
        self.tree.pack(fill="both", expand=True, padx=8, pady=8)

        btns = ttk.Frame(self); btns.pack(fill="x", padx=8, pady=(0,8))
        ttk.Button(btns, text="Run All", command=self.run_all).pack(side="left")
        ttk.Button(btns, text="Close",   command=self.master.destroy).pack(side="right")

        for tc in self.tests:
            self.tree.insert("", "end", values=(tc.cipher, tc.title, "pending"))

    def run_all(self):
        for i, tc in enumerate(self.tests):
            try:
                # Prefer decode(ct) → pt check; fall back to encode(pt)
                if tc.ct is not None and tc.dec is not None:
                    got = call_decode(tc.cipher, tc.ct, tc.params)
                    lhs = tc.normalizer(got) if tc.normalizer else got
                    rhs = tc.normalizer(tc.pt) if (tc.pt and tc.normalizer) else (tc.pt or got)
                    ok = (lhs == rhs)
                elif tc.pt is not None and tc.enc is not None:
                    got = call_encode(tc.cipher, tc.pt, tc.params)
                    lhs = tc.normalizer(got) if tc.normalizer else got
                    rhs = tc.normalizer(tc.ct) if (tc.ct and tc.normalizer) else (tc.ct or got)
                    ok = (lhs == rhs)
                else:
                    ok = False
                res = "PASS" if ok else "FAIL"
            except Exception as e:
                res = f"ERR: {e}"
            item_id = self.tree.get_children()[i]
            vals = list(self.tree.item(item_id, "values"))
            vals[2] = res
            self.tree.item(item_id, values=vals)

# Hook into the GUI
def _open_test_bench(self):
    win = tk.Toplevel(self.root)
    win.title("Test Bench")
    win.geometry("620x360")
    tb = TestBench(win)
    tb.pack(fill="both", expand=True)

# attach method to CipherGUI later in _build_menu patch



# ---- runner -----------------------------------------------------------------
class TestResult:
    __slots__ = ("family","name","ok","pt","ct","err","elapsed","note")
    def __init__(self, family,name, ok, pt, ct, err, elapsed, note=""):
        self.family=family; self.name=name; self.ok=ok
        self.pt=pt; self.ct=ct; self.err=err; self.elapsed=elapsed; self.note=note

def _run_one_test(tc: TestCase) -> TestResult:
    t0 = time.time()
    note = ""
    try:
        if tc.mode == "roundtrip":
            if not (tc.enc_fn and tc.dec_fn):
                return TestResult(tc.family, tc.name, False, "", "", "Missing enc/dec", 0.0)
            ok, enc = _safe_call(tc.enc_fn, tc.pt, **tc.params)
            if not ok:
                return TestResult(tc.family, tc.name, False, "", "", f"EncErr:{enc}", time.time()-t0)
            ct = enc
            ok, dec = _safe_call(tc.dec_fn, ct, **tc.params)
            if not ok:
                return TestResult(tc.family, tc.name, False, "", ct if isinstance(ct,str) else str(ct),
                                  f"DecErr:{dec}", time.time()-t0)
            pt2 = dec
            good = (tc.normalizer(pt2) == tc.normalizer(tc.pt))
            return TestResult(tc.family, tc.name, good, str(pt2), str(ct), "" if good else "Mismatch", time.time()-t0)

        elif tc.mode == "decode_only":
            # Known CT -> expected PT (in tc.pt)
            dec_fn = tc.dec_fn
            if dec_fn is None:
                return TestResult(tc.family, tc.name, False, "", tc.ref_ct, "No decoder", time.time()-t0)
            ok, dec = _safe_call(dec_fn, tc.ref_ct, **tc.params)
            if not ok:
                return TestResult(tc.family, tc.name, False, "", tc.ref_ct, f"DecErr:{dec}", time.time()-t0)
            pt2 = dec
            good = (tc.normalizer(pt2) == tc.normalizer(tc.pt))
            return TestResult(tc.family, tc.name, good, str(pt2), str(tc.ref_ct), "" if good else "Mismatch", time.time()-t0)

        else:
            return TestResult(tc.family, tc.name, False, "", "", f"Unknown mode {tc.mode}", time.time()-t0)
    except Exception as e:
        return TestResult(tc.family, tc.name, False, "", "", f"Err:{e}", time.time()-t0)

# ---- GUI: Test Bench window / tab -------------------------------------------
class TestBench(ttk.Frame):
    COLS = ("Family","Name","OK","Ciphertext","Plaintext","Error","ms")
    def __init__(self, master, **kw):
        super().__init__(master, **kw)
        self.tests = _build_tests()
        self.results = []
        self._make_ui()

    def _make_ui(self):
        top = ttk.Frame(self); top.pack(fill="x", padx=10, pady=(10,6))
        ttk.Label(top, text=f"Discovered tests: {len(self.tests)}", font=("TkDefaultFont",10,"bold")).pack(side="left")
        self.only_failed = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Show failed only", variable=self.only_failed, command=self._refresh_view).pack(side="left", padx=10)

        btns = ttk.Frame(top); btns.pack(side="right")
        ttk.Button(btns, text="Run All", command=self.run_all).pack(side="left", padx=4)
        ttk.Button(btns, text="Run Failed", command=self.run_failed).pack(side="left", padx=4)
        ttk.Button(btns, text="Export CSV", command=self.export_csv).pack(side="left", padx=4)
        ttk.Button(btns, text="Copy Console Summary", command=self.copy_console_summary).pack(side="left", padx=4)

        mid = ttk.Frame(self); mid.pack(fill="both", expand=True, padx=10, pady=6)
        self.tree = ttk.Treeview(mid, columns=self.COLS, show="headings", height=16)
        for c in self.COLS:
            self.tree.heading(c, text=c)
            width = 110 if c in ("Family","Name","OK","ms") else 300
            self.tree.column(c, width=width, anchor="w")
        yscroll = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=yscroll.set)
        self.tree.pack(side="left", fill="both", expand=True)
        yscroll.pack(side="left", fill="y")

        # row styles
        style = ttk.Style(self)
        style.map("Ok.Treeview", background=[("selected","#2e7")])
        style.map("Fail.Treeview", background=[("selected","#f96")])
        # progress
        bottom = ttk.Frame(self); bottom.pack(fill="x", padx=10, pady=(0,10))
        self.pb = ttk.Progressbar(bottom, maximum=max(1,len(self.tests)))
        self.pb.pack(fill="x")

        self._refresh_view()

    def _refresh_view(self):
        self.tree.delete(*self.tree.get_children())
        for r in self.results or []:
            if self.only_failed.get() and r.ok:
                continue
            tag = ("pass",) if r.ok else ("fail",)
            oktext = "✔" if r.ok else "✖"
            ms = f"{int(r.elapsed*1000)}"
            self.tree.insert("", "end", values=(r.family, r.name, oktext, r.ct, r.pt, r.err, ms), tags=tag)
        self.tree.tag_configure("pass", background="#eaffea")
        self.tree.tag_configure("fail", background="#ffecec")

    def run_all(self):
        self.results = []
        self.pb["value"]=0
        self.update_idletasks()
        out_lines=[]
        # Classic console banner (like user log)
        print("="*8, "TEST BENCH RUN", "="*8)
        fam_groups={}
        for i,tc in enumerate(self.tests, 1):
            r = _run_one_test(tc)
            self.results.append(r)
            fam_groups.setdefault(r.family, []).append(r)
            self.pb["value"]=i
            self._refresh_view()
            self.update_idletasks()
            # Print per-family line compactly like the original style
        # Emit a summary block per family to console
        for fam, rows in fam_groups.items():
            okc = sum(1 for x in rows if x.ok)
            tot = len(rows)
            # print a representative line (first) like earlier logs
            rep = rows[0]
            ct_show = (rep.ct[:60] + "…") if len(rep.ct)>60 else rep.ct
            pt_show = (rep.pt[:40] + "…") if len(rep.pt)>40 else rep.pt
            print(f"{fam:<13} ok={str(okc==tot):<5}  ct={ct_show}  pt={pt_show}")
        print("Summary:", f"Families tested: {len(fam_groups)}. Total cases: {len(self.tests)}. Passes:", sum(1 for r in self.results if r.ok), "/", len(self.tests))

    def run_failed(self):
        if not self.results:
            return self.run_all()
        failed = [t for t,r in zip(self.tests,self.results) if not r.ok]
        if not failed:
            messagebox.showinfo("Run Failed", "No failed tests to re-run.")
            return
        # temporarily restrict tests to failed, run, then re-expand
        orig_tests = self.tests
        self.tests = failed
        try:
            self.run_all()
        finally:
            self.tests = orig_tests

    def export_csv(self):
        if fd is None:
            messagebox.showerror("Export CSV", "File dialog not available.")
            return
        path = fd.asksaveasfilename(title="Export Test Results", defaultextension=".csv",
                                    filetypes=[("CSV","*.csv"),("All files","*.*")])
        if not path: return
        with open(path,"w",newline="",encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["Family","Name","OK","Ciphertext","Plaintext","Error","ms"])
            for r in self.results:
                w.writerow([r.family, r.name, r.ok, r.ct, r.pt, r.err, int(r.elapsed*1000)])
        messagebox.showinfo("Export CSV", f"Saved to:\n{path}")

    def copy_console_summary(self):
        # Generate the classic console summary and copy to clipboard
        fam_groups={}
        for r in self.results:
            fam_groups.setdefault(r.family, []).append(r)
        buf = io.StringIO()
        for fam, rows in fam_groups.items():
            okc = sum(1 for x in rows if x.ok)
            tot = len(rows)
            rep = rows[0]
            ct_show = (rep.ct[:60] + "…") if isinstance(rep.ct,str) and len(rep.ct)>60 else rep.ct
            pt_show = (rep.pt[:40] + "…") if isinstance(rep.pt,str) and len(rep.pt)>40 else rep.pt
            buf.write(f"{fam:<13} ok={str(okc==tot):<5}  ct={ct_show}  pt={pt_show}\n")
        buf.write(f"Summary: Families tested: {len(fam_groups)}. Total cases: {len(self.tests)}. Passes: {sum(1 for r in self.results if r.ok)}/{len(self.tests)}\n")
        try:
            self.clipboard_clear()
            self.clipboard_append(buf.getvalue())
            messagebox.showinfo("Copied", "Console-style summary copied to clipboard.")
        except Exception:
            # fall back: print
            print(buf.getvalue())

# ---- hook into GUI: add tab if Notebook exists; otherwise a Tools→Test Bench ---
def _install_test_tab():
    if 'CipherGUI' not in globals():
        # fallback: create a simple launcher function
        def _open_standalone_test():
            root = tk.Toplevel()
            root.title("Test Bench")
            frm = TestBench(root)
            frm.pack(fill="both", expand=True)
            root.geometry("1024x520")
        globals()["_open_test_bench_window"] = _open_standalone_test
        return

    # Wrap the menu to add Tools → Test Bench
    if not hasattr(CipherGUI, "_build_menu_original_test"):
        CipherGUI._build_menu_original_test = CipherGUI._build_menu
        def _build_menu_wrap(self):
            CipherGUI._build_menu_original_test(self)
            mbar = self.root.nametowidget(self.root['menu'])
            # ensure a Tools menu exists
            tools = tk.Menu(mbar, tearoff=0)
            tools.add_command(label="Test Bench…", command=lambda: self.open_test_bench())
            mbar.add_cascade(label="Tools", menu=tools)
        CipherGUI._build_menu = _build_menu_wrap

    # Add method to open test bench window
    if not hasattr(CipherGUI, "open_test_bench"):
        def open_test_bench(self):
            win = tk.Toplevel(self.root)
            win.title("Test Bench")
            tab = TestBench(win)
            tab.pack(fill="both", expand=True)
            win.geometry("1100x560")
        CipherGUI.open_test_bench = open_test_bench

    # If the app uses a Notebook and has a known attribute, try adding a tab on startup
    if not hasattr(CipherGUI, "_post_layout_original_testtab"):
        old = getattr(CipherGUI, "_post_layout", lambda self: None)
        def _post_layout_wrap(self):
            try: old(self)
            except Exception: pass
            # attach as a tab if we can find a ttk.Notebook
            nb = None
            # try common attribute names
            for attr in ("notebook","nb","tabs","main_nb"):
                obj = getattr(self, attr, None)
                if isinstance(obj, ttk.Notebook):
                    nb = obj; break
            if nb is not None:
                frame = ttk.Frame(nb)
                bench = TestBench(frame)
                bench.pack(fill="both", expand=True)
                nb.add(frame, text="Tests")
        CipherGUI._post_layout = _post_layout_wrap

_install_test_tab()


if __name__ == "__main__":
    # If any CLI args: run CLI. Else: launch GUI (if available).
    if len(sys.argv) > 1:
        sys.exit(cli_main(sys.argv[1:]))
    else:
        try:
            if tk is not None:
                launch_gui()
            else:
                # Fallback: print list
                print("Tkinter not found. Use CLI. Example:")
                print("  python encripter.py list")
                print("  python encripter.py encode Caesar \"HELLO\" -p shift=5")
                print("  python encripter.py guess \"Gur dhvpx oebja sbk\"")
        except KeyboardInterrupt:
            pass
