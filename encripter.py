#!/usr/bin/env python3
"""
Encryptor & Decryptor — improved guessers + heavy-duty + progress + fixed columnar
Save as encryptor_full_improved.py and run with Python 3.8+ (works with 3.13+).
"""
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import base64, string, urllib.parse, re, random, time, os, math
from collections import Counter, deque
import concurrent.futures, threading

# detect platform worker cap (Windows)
try:
    from concurrent.futures.process import _MAX_WINDOWS_WORKERS as _PLATFORM_MAX_WORKERS
except Exception:
    _PLATFORM_MAX_WORKERS = 61

# -----------------------
# Config / Globals
# -----------------------
REPEAT_XOR_MAX = 12
USE_PROCESS_POOL_DEFAULT = True
MAX_WORKERS_DEFAULT = max(1, min(8, (os.cpu_count() or 2)))
AFFINE_VALID_A = [1,3,5,7,9,11,15,17,19,21,23,25]
PLAYFAIR_META_MARKER = '\u00A4'

# -----------------------
# Utils
# -----------------------
def _clamp_workers(requested):
    try:
        cpu = max(1, os.cpu_count() or 1)
    except Exception:
        cpu = 1
    platform_max = int(_PLATFORM_MAX_WORKERS or 61)
    return max(1, min(requested, platform_max, max(2, cpu*2)))

def _modinv(a, m=26):
    a %= m
    for x in range(1, m):
        if (a * x) % m == 1:
            return x
    raise ValueError("No modular inverse")

def _shift_char(c, shift):
    if 'A' <= c <= 'Z': return chr((ord(c)-65 + shift) % 26 + 65)
    if 'a' <= c <= 'z': return chr((ord(c)-97 + shift) % 26 + 97)
    return c

def _letters_only(s): return ''.join(ch for ch in s if ch.isalpha())
def _preserve_case(orig, repl): return repl.upper() if orig.isupper() else repl.lower()

# -----------------------
# Encodings / Basics
# -----------------------
def caesar_cipher(text, shift): return ''.join(_shift_char(c, shift) for c in text)
def caesar_decrypt(text, shift): return caesar_cipher(text, -shift)
def reverse_cipher(text): return text[::-1]
def rot13(text): return caesar_cipher(text, 13)
def rot47(text):
    out=[]
    for ch in text:
        o=ord(ch)
        if 33<=o<=126: out.append(chr(33+((o-33+47)%94)))
        else: out.append(ch)
    return ''.join(out)
def atbash_cipher(text):
    out=[]
    for c in text:
        if 'A'<=c<='Z': out.append(chr(65+(25-(ord(c)-65))))
        elif 'a'<=c<='z': out.append(chr(97+(25-(ord(c)-97))))
        else: out.append(c)
    return ''.join(out)

def base64_decrypt(text):
    try: return base64.b64decode(text.encode()).decode()
    except Exception: return None
def b64url_encode(text): return base64.urlsafe_b64encode(text.encode()).decode()
def b64url_decode(text):
    try:
        pad = '=' * (-len(text) % 4)
        return base64.urlsafe_b64decode((text + pad).encode()).decode()
    except Exception: return None
def base32_encode(text): return base64.b32encode(text.encode()).decode()
def base32_decode(text):
    try: return base64.b32decode(text.encode()).decode()
    except Exception: return None
def a85_encode(text): return base64.a85encode(text.encode()).decode()
def a85_decode(text):
    try: return base64.a85decode(text.encode()).decode()
    except Exception: return None
def url_encode(text): return urllib.parse.quote_plus(text)
def url_decode(text):
    try: return urllib.parse.unquote_plus(text)
    except Exception: return None
def hex_decrypt(text):
    try: return bytes.fromhex(text).decode()
    except Exception: return None
def binary_decrypt(text):
    try:
        parts = text.split()
        return ''.join(chr(int(b,2)) for b in parts)
    except Exception: return None

# -----------------------
# Vigenere-family & keyed
# -----------------------
def vigenere_encrypt(text, key):
    key_letters=[k for k in (key or '') if k.isalpha()]
    if not key_letters: raise ValueError("Vigenere needs letters")
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k=key_letters[ki%len(key_letters)]
            shift = ord(k.lower())-97
            res.append(_shift_char(c, shift)); ki+=1
        else: res.append(c)
    return ''.join(res)

def vigenere_decrypt(text, key):
    key_letters=[k for k in (key or '') if k.isalpha()]
    if not key_letters: raise ValueError("Vigenere needs letters")
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k=key_letters[ki%len(key_letters)]
            shift = ord(k.lower())-97
            res.append(_shift_char(c, -shift)); ki+=1
        else: res.append(c)
    return ''.join(res)

def autokey_encrypt(text, key):
    key_letters=[k for k in (key or '') if k.isalpha()]
    if not key_letters: raise ValueError("Autokey needs letters")
    stream = key_letters + [c for c in text if c.isalpha()]
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k = stream[ki]; shift = ord(k.lower())-97
            res.append(_shift_char(c, shift)); ki+=1
        else: res.append(c)
    return ''.join(res)

def autokey_decrypt(text, key):
    key_letters=[k.lower() for k in (key or '') if k.isalpha()]
    if not key_letters: raise ValueError("Autokey needs letters")
    res=[]; recovered=[]; j=0
    for ch in text:
        if ch.isalpha():
            if j < len(key_letters): k = key_letters[j]
            else:
                idx = j-len(key_letters)
                k = recovered[idx] if idx < len(recovered) else 'a'
            shift=(ord(k)-97)%26
            p=_shift_char(ch, -shift)
            res.append(p); recovered.append(p.lower() if p.isalpha() else 'a'); j+=1
        else: res.append(ch)
    return ''.join(res)

def runningkey_encrypt(text, key_text):
    key_letters=[k for k in (key_text or '') if k.isalpha()]
    if not key_letters: raise ValueError("Running key needs letters")
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k=key_letters[ki%len(key_letters)]; shift=(ord(k.lower())-97)%26
            res.append(_shift_char(c, shift)); ki+=1
        else: res.append(c)
    return ''.join(res)

def runningkey_decrypt(text, key_text):
    key_letters=[k for k in (key_text or '') if k.isalpha()]
    if not key_letters: raise ValueError("Running key needs letters")
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k=key_letters[ki%len(key_letters)]; shift=(ord(k.lower())-97)%26
            res.append(_shift_char(c, -shift)); ki+=1
        else: res.append(c)
    return ''.join(res)

def beaufort(text, key):
    key_letters=[k for k in (key or '') if k.isalpha()]
    if not key_letters: raise ValueError("Beaufort needs letters")
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k=key_letters[ki%len(key_letters)]; kshift=(ord(k.lower())-97)%26
            base = ord('A') if c.isupper() else ord('a')
            x = ord(c)-base; y = (kshift - x) % 26
            res.append(chr(base+y)); ki+=1
        else: res.append(c)
    return ''.join(res)

def porta(text, key):
    key_letters=[k for k in (key or '') if k.isalpha()]
    if not key_letters: raise ValueError("Porta needs letters")
    res=[]; ki=0
    for c in text:
        if c.isalpha():
            k=key_letters[ki%len(key_letters)]; kidx=(ord(k.lower())-97)//2
            base = ord('A') if c.isupper() else ord('a')
            x = ord(c)-base
            if x<13: y=(x+13-kidx)%13 + 13
            else: y=(x-13+kidx)%13
            res.append(chr(base+y)); ki+=1
        else: res.append(c)
    return ''.join(res)

# -----------------------
# Affine / Rail / XOR
# -----------------------
def affine_encrypt(text,a,b):
    a=int(a); b=int(b)
    if a not in AFFINE_VALID_A: raise ValueError("a must be coprime with 26")
    out=[]
    for c in text:
        if c.isalpha():
            base = ord('A') if c.isupper() else ord('a')
            x = ord(c)-base; y=(a*x + b)%26; out.append(chr(base+y))
        else: out.append(c)
    return ''.join(out)

def affine_decrypt(text,a,b):
    a=int(a); b=int(b)
    if a not in AFFINE_VALID_A: raise ValueError("a must be coprime with 26")
    a_inv = _modinv(a,26)
    out=[]
    for c in text:
        if c.isalpha():
            base = ord('A') if c.isupper() else ord('a')
            y=ord(c)-base; x=(a_inv*(y-b))%26; out.append(chr(base+x))
        else: out.append(c)
    return ''.join(out)

def xor_encrypt_to_hex(text, key):
    if not key: raise ValueError("XOR needs key")
    kb = key.encode()
    tb = text.encode(errors='replace')
    out = bytes(tb[i] ^ kb[i % len(kb)] for i in range(len(tb)))
    return out.hex()

def xor_decrypt_from_hex(hex_text, key):
    if not key: raise ValueError("XOR needs key")
    try:
        data = bytes.fromhex(hex_text)
    except Exception:
        return None
    kb = key.encode()
    out = bytes(data[i] ^ kb[i % len(kb)] for i in range(len(data)))
    try: return out.decode()
    except UnicodeDecodeError: return out.decode(errors='replace')

def rail_fence_encrypt(text, rails):
    rails=int(rails)
    if rails<2: return text
    fence=[[] for _ in range(rails)]; r=0; d=1
    for ch in text:
        fence[r].append(ch)
        r+=d
        if r==0 or r==rails-1: d*=-1
    return ''.join(''.join(rw) for rw in fence)

def rail_fence_decrypt(cipher, rails):
    rails=int(rails)
    if rails<2: return cipher
    pattern=[]; r=0; d=1
    for _ in cipher:
        pattern.append(r); r+=d
        if r==0 or r==rails-1: d*=-1
    counts=[pattern.count(i) for i in range(rails)]
    idx=0; cols=[]
    for c in counts:
        cols.append(list(cipher[idx:idx+c])); idx+=c
    pointers=[0]*rails; out=[]
    for p in pattern:
        out.append(cols[p][pointers[p]]); pointers[p]+=1
    return ''.join(out)

# -----------------------
# Morse & Bacon
# -----------------------
MORSE_MAP = { 'A':'.-','B':'-...','C':'-.-.','D':'-..','E':'.','F':'..-.',
    'G':'--.','H':'....','I':'..','J':'.---','K':'-.-','L':'.-..',
    'M':'--','N':'-.','O':'---','P':'.--.','Q':'--.-','R':'.-.',
    'S':'...','T':'-','U':'..-','V':'...-','W':'.--','X':'-..-',
    'Y':'-.--','Z':'--..','0':'-----','1':'.----','2':'..---',
    '3':'...--','4':'....-','5':'.....','6':'-....','7':'--...',
    '8':'---..','9':'----.','.':'.-.-.-',',':'--..--','?':'..--..',
    "'":'.----.','!':'-.-.--','/':'-..-.','(':'-.--.',')':'-.--.-',
    '&':'.-...',';':'-.-.-.','=':'-...-','+':'.-.-.','-':'-....-',
    '_':'..--.-','"':'.-..-.','$':'...-..-','@':'.--.-.',' ':'/' }
MORSE_INV = {v:k for k,v in MORSE_MAP.items()}
def morse_encode(text): return ' '.join(MORSE_MAP.get(ch.upper(), ch) for ch in text)
def morse_decode(text):
    try:
        parts = text.split(' ')
        out=[]
        for p in parts:
            if p=='': continue
            out.append(MORSE_INV.get(p,'?'))
        return ''.join(out).replace('/', ' ')
    except Exception: return None

BACON_MAP = { 'A':'AAAAA','B':'AAAAB','C':'AAABA','D':'AAABB','E':'AABAA','F':'AABAB','G':'AABBA','H':'AABBB',
 'I':'ABAAA','J':'ABAAB','K':'ABABA','L':'ABABB','M':'ABBAA','N':'ABBAB','O':'ABBBA','P':'ABBBB',
 'Q':'BAAAA','R':'BAAAB','S':'BAABA','T':'BAABB','U':'BABAA','V':'BABAB','W':'BABBA','X':'BABBB',
 'Y':'BBAAA','Z':'BBAAB',' ':'BBBBB' }
BACON_INV = {v:k for k,v in BACON_MAP.items()}
def bacon_encode(text): return ' '.join(BACON_MAP.get(ch.upper(),'BBBBB') for ch in text)
def bacon_decode(text):
    parts = text.split()
    out=[]
    for p in parts:
        out.append(BACON_INV.get(p.upper(), '?'))
    return ''.join(out)
def bacon_decode_loose(text):
    t=''.join(ch for ch in text.upper() if ch in 'AB')
    if len(t)<5: return None
    groups=[t[i:i+5] for i in range(0,len(t)-(len(t)%5),5)]
    if not groups: return None
    return bacon_decode(' '.join(groups))

# -----------------------
# Playfair (improved & preserve)
# -----------------------
def _prep_playfair_grid_list(key):
    key = ''.join(ch.lower() for ch in (key or '') if ch.isalpha()).replace('j','i')
    seen=[]
    for ch in key + ''.join(c for c in string.ascii_lowercase if c!='j'):
        if ch not in seen: seen.append(ch)
    return seen

def _pairs_from_letters(letters):
    t = letters
    out=[]; i=0
    while i < len(t):
        a = t[i]
        b = t[i+1] if i+1 < len(t) else None
        if b is None:
            out.append((a,'x')); i+=1
        elif a==b:
            out.append((a,'x')); i+=1
        else:
            out.append((a,b)); i+=2
    return out

def _encrypt_letters_playfair(letters,key):
    letters = ''.join(ch.lower().replace('j','i') for ch in letters if ch.isalpha())
    if not letters: return ''
    grid=_prep_playfair_grid_list(key)
    out=[]
    for a,b in _pairs_from_letters(letters):
        ia=grid.index(a); ib=grid.index(b)
        ra,ca = divmod(ia,5); rb,cb = divmod(ib,5)
        if ra==rb:
            out.append(grid[ra*5 + (ca+1)%5]); out.append(grid[rb*5 + (cb+1)%5])
        elif ca==cb:
            out.append(grid[((ra+1)%5)*5 + ca]); out.append(grid[((rb+1)%5)*5 + cb])
        else:
            out.append(grid[ra*5 + cb]); out.append(grid[rb*5 + ca])
    return ''.join(out)

def _decrypt_letters_playfair_raw(enc_letters,key):
    letters = ''.join(ch.lower().replace('j','i') for ch in enc_letters if ch.isalpha())
    if not letters: return ''
    if len(letters)%2==1: letters += 'x'
    grid=_prep_playfair_grid_list(key)
    out=[]
    for i in range(0,len(letters),2):
        a,b = letters[i], letters[i+1]
        ia=grid.index(a); ib=grid.index(b)
        ra,ca = divmod(ia,5); rb,cb = divmod(ib,5)
        if ra==rb:
            out.append(grid[ra*5 + (ca-1)%5]); out.append(grid[rb*5 + (cb-1)%5])
        elif ca==cb:
            out.append(grid[((ra-1)%5)*5 + ca]); out.append(grid[((rb-1)%5)*5 + cb])
        else:
            out.append(grid[ra*5 + cb]); out.append(grid[rb*5 + ca])
    return ''.join(out)

def _clean_playfair_plain(raw_plain):
    out=[]; i=0; s=raw_plain
    while i < len(s):
        if i+2 < len(s) and s[i]==s[i+2] and s[i+1]=='x':
            out.append(s[i]); out.append(s[i+2]); i+=3
        else:
            out.append(s[i]); i+=1
    s2=''.join(out)
    if s2.endswith('x'): s2=s2[:-1]
    return s2

def playfair_encrypt_preserve(plaintext,key):
    letters_positions=[i for i,ch in enumerate(plaintext) if ch.isalpha()]
    if not letters_positions: return plaintext
    letters=''.join(plaintext[i].lower() for i in letters_positions)
    j_positions=[idx for idx,ch in enumerate(letters) if ch=='j']
    letters_for = letters.replace('j','i')
    enc_letters = _encrypt_letters_playfair(letters_for, key)
    out=list(plaintext)
    for idx,pos in enumerate(letters_positions):
        ch = enc_letters[idx] if idx < len(enc_letters) else 'x'
        out[pos] = ch.upper() if plaintext[pos].isupper() else ch
    cipher=''.join(out)
    tail=''
    if len(enc_letters) > len(letters_for) or j_positions:
        tail = PLAYFAIR_META_MARKER + ''.join(enc_letters[len(letters_for):]) + '|' + ';'.join(str(x) for x in j_positions)
        cipher = cipher + tail
    return cipher

def playfair_decrypt_preserve(ciphertext,key):
    tail=''; j_positions=[]
    if PLAYFAIR_META_MARKER in ciphertext:
        ciphertext, meta = ciphertext.split(PLAYFAIR_META_MARKER,1)
        parts = meta.split('|',1)
        tail = ''.join(ch.lower() for ch in parts[0] if ch.isalpha()) if parts[0] else ''
        if len(parts) > 1 and parts[1]:
            j_positions=[int(x) for x in parts[1].split(';') if x!='']
    letters_positions=[i for i,ch in enumerate(ciphertext) if ch.isalpha()]
    if not letters_positions: return ciphertext
    cipher_letters=''.join(ciphertext[i].lower() for i in letters_positions)
    full_enc = cipher_letters + tail
    raw_plain = _decrypt_letters_playfair_raw(full_enc, key)
    clean_plain = _clean_playfair_plain(raw_plain)
    pl=list(clean_plain)
    for idx in j_positions:
        if 0<=idx < len(pl): pl[idx] = 'j'
    out=list(ciphertext)
    for idx,pos in enumerate(letters_positions):
        ch = pl[idx] if idx < len(pl) else 'x'
        out[pos] = ch.upper() if ciphertext[pos].isupper() else ch
    return ''.join(out)

def playfair_encrypt_letters_only(text,key):
    letters = ''.join(ch for ch in text if ch.isalpha())
    return _encrypt_letters_playfair(letters, key)

def playfair_decrypt_letters_only(text,key):
    raw = _decrypt_letters_playfair_raw(text, key)
    return _clean_playfair_plain(raw)

# -----------------------
# Columnar transposition (fixed)
# -----------------------
def _column_order_from_key(key):
    # produce order indexes: for key "ZEBRAS" returns order indexes for each column position
    k = ''.join(ch for ch in key if ch.isalpha()).lower()
    if not k:
        raise ValueError("Columnar key must contain letters")
    pairs = sorted([(ch, i) for i,ch in enumerate(k)])
    order = [0]*len(k)
    for rank,(_, idx) in enumerate(pairs):
        order[idx] = rank
    return order

def columnar_encrypt(text, key):
    order = _column_order_from_key(key)
    ncols = len(order)
    # fill rows left->right with plaintext; pad with spaces
    rows = []
    row = []
    for ch in text:
        row.append(ch)
        if len(row) == ncols:
            rows.append(row); row=[]
    if row:
        while len(row) < ncols: row.append(' ')
        rows.append(row)
    # read columns in order by rank 0..ncols-1
    ciphertext = []
    for rank in range(ncols):
        col_idx = order.index(rank)
        for r in rows:
            ciphertext.append(r[col_idx])
    return ''.join(ciphertext)

def columnar_decrypt(cipher, key):
    order = _column_order_from_key(key)
    ncols = len(order)
    nrows = (len(cipher) + ncols - 1) // ncols
    # determine column lengths:
    # basic approach: each column has either nrows or nrows-1 characters
    total = len(cipher)
    base_len = total // ncols
    extra = total % ncols
    col_lengths = [base_len + (1 if order[i] < extra else 0) for i in range(ncols)]
    # But previous method of assigning by rank is easier:
    parts = [None]*ncols
    pos = 0
    for rank in range(ncols):
        col_idx = order.index(rank)
        L = col_lengths[col_idx]
        parts[col_idx] = list(cipher[pos:pos+L])
        pos += L
    rows = []
    for r in range(max(len(p) for p in parts)):
        row = []
        for c in range(ncols):
            if r < len(parts[c]): row.append(parts[c][r])
            else: row.append(' ')
        rows.append(row)
    plain = ''.join(''.join(r) for r in rows).rstrip()
    return plain

# -----------------------
# Keyword lists
# -----------------------
def _load_keywords_fallback():
    return ['password','secret','access','login','admin','user','hello','world','attack','the','and','to','of','in','is','token','lemon','shadow','knight']
KEYWORD_MATCH_LIST = _load_keywords_fallback()
KEY_TRY_LIST = [
    'secret','password','key','admin','user','test','hello','dragon','castle','lemon','shadow','knight','alpha','delta','fort','keyword','monarchy','silver'
]

# -----------------------
# Scoring & Vigenere improvements
# -----------------------
ENGLISH_FREQ = [0.08167,0.01492,0.02782,0.04253,0.12702,0.02228,0.02015,0.06094,0.06966,0.00153,0.00772,0.04025,0.02406,0.06749,0.07507,0.01929,0.00095,0.05987,0.06327,0.09056,0.02758,0.00978,0.02360,0.00150,0.01974,0.00074]
ENGLISH_FREQ_MAP = {ch:f for ch,f in zip(string.ascii_lowercase, ENGLISH_FREQ)}

def _score_english_simple(text: str) -> float:
    if not text: return -999.0
    s = text.lower()
    letters = [c for c in s if 'a' <= c <= 'z']
    n=len(letters)
    if n==0: return -999.0
    counts=Counter(letters)
    score=0.0
    for ch,freq in ENGLISH_FREQ_MAP.items():
        observed = counts.get(ch,0)/n
        score -= abs(observed - freq)
    if ' the ' in s: score += 0.9
    if ' and ' in s: score += 0.4
    nonprint = sum(1 for ch in text if ord(ch) < 32 and ch not in '\r\n\t')
    score -= nonprint*0.6
    # prefer printable ratio
    printable = sum(1 for ch in text if 32 <= ord(ch) <= 126)
    score += (printable / max(1, len(text))) * 0.2
    return score

def _ic(text):
    t = [c for c in text.upper() if 'A'<=c<='Z']
    n=len(t)
    if n<2: return 0.0
    counts=Counter(t)
    num=sum(f*(f-1) for f in counts.values()); den=n*(n-1)
    return num/den if den else 0.0

def _avg_ic_for_keylen(text, keylen):
    t=''.join(c for c in text.upper() if 'A'<=c<='Z')
    if keylen<=0: return 0.0
    ics=[]
    for i in range(keylen):
        slice_i = t[i::keylen]
        ics.append(_ic(slice_i))
    return sum(ics)/len(ics) if ics else 0.0

def _kasiski_candidates(text, nmin=3, nmax=5, max_len=30):
    t=''.join(c for c in text.upper() if 'A'<=c<='Z')
    distances=[]
    for n in range(nmin,nmax+1):
        seen={}
        for i in range(len(t)-n+1):
            sub = t[i:i+n]
            if sub in seen: distances.append(i-seen[sub])
            seen[sub]=i
    factor_counts=Counter()
    for d in distances:
        for k in range(2, max_len+1):
            if d % k == 0: factor_counts[k]+=1
    return [k for k,_ in factor_counts.most_common(20)]

def _ic_candidates(text, max_len=30):
    vals=[]
    for k in range(1, max_len+1):
        aic = _avg_ic_for_keylen(text, k)
        score = -abs(aic - 0.0667) + abs(aic - 0.0385)
        vals.append((score,k))
    vals.sort(reverse=True)
    return [k for _,k in vals[:20]]

def _chi_square_for_shift(seq_upper, shift):
    filtered = [((ord(c)-65 - shift) % 26) for c in seq_upper if 'A'<=c<='Z']
    n = len(filtered)
    if n==0: return float('inf')
    counts=[0]*26
    for idx in filtered: counts[idx]+=1
    chi=0.0
    for i in range(26):
        expected = ENGLISH_FREQ[i]*n
        if expected>0: chi += (counts[i]-expected)**2 / expected
    return chi

def _derive_vigenere_key(text, keylen):
    t=''.join(c for c in text.upper() if 'A'<=c<='Z')
    if keylen<=0: return ''
    key_chars=[]
    for i in range(keylen):
        slice_i = ''.join(t[j] for j in range(i,len(t),keylen))
        best_shift, best_chi = 0, float('inf')
        for s in range(26):
            chi = _chi_square_for_shift(slice_i, s)
            if chi < best_chi:
                best_chi, best_shift = chi, s
        key_chars.append(chr(ord('a') + best_shift))
    return ''.join(key_chars)

def guess_vigenere_keys(text, max_len=24, top=16, heavy=False, time_limit=None):
    kas = _kasiski_candidates(text, max_len=max_len)
    ics = _ic_candidates(text, max_len=max_len)
    combo=[]
    for k in kas + ics:
        if k not in combo and 1<=k<=max_len: combo.append(k)
    candidates=[]
    for klen in combo[:min(len(combo), 40)]:
        key = _derive_vigenere_key(text, klen)
        if key:
            aic = _avg_ic_for_keylen(text, klen)
            candidates.append((key, klen, aic))
    for k in KEY_TRY_LIST:
        candidates.append((k, len([c for c in k if c.isalpha()]), 0.0))
    for _ in range(20):
        k = ''.join(random.choice(string.ascii_lowercase) for _ in range(random.randint(2,6)))
        candidates.append((k, len(k), 0.0))
    candidates.sort(key=lambda x: x[2], reverse=True)
    seen=set(); out=[]
    start = time.time()
    # refine with hillclimb + optional simulated annealing if heavy
    for key,klen,aic in candidates:
        if key in seen: continue
        seen.add(key)
        # score plaintext
        try:
            pt = vigenere_decrypt(text, key)
        except Exception:
            continue
        best_key = key; best_score = _score_english_simple(pt)
        # hill-climb local improvements
        t0 = time.time()
        limit = 4.0 if not heavy else (time_limit or 8.0)
        while time.time()-t0 < limit:
            improved=False
            for pos in range(len(best_key)):
                for c in string.ascii_lowercase:
                    if c == best_key[pos]: continue
                    cand = best_key[:pos]+c+best_key[pos+1:]
                    try:
                        ptcand = vigenere_decrypt(text, cand)
                    except Exception: continue
                    sc = _score_english_simple(ptcand)
                    if sc > best_score:
                        best_score = sc; best_key = cand; improved=True; break
                if improved: break
            if not improved:
                # small random mutation if heavy
                if heavy:
                    pos = random.randrange(len(best_key))
                    c = random.choice(string.ascii_lowercase)
                    best_key = best_key[:pos]+c+best_key[pos+1:]
                else:
                    break
        # optional simulated annealing (time-boxed)
        if heavy:
            T0 = 1.0
            t_limit = time_limit or 30.0
            start_sa = time.time()
            cur_key = best_key; cur_score = best_score
            while time.time()-start_sa < t_limit:
                pos = random.randrange(len(cur_key))
                c = random.choice(string.ascii_lowercase)
                cand = cur_key[:pos]+c+cur_key[pos+1:]
                try:
                    ptcand = vigenere_decrypt(text, cand)
                except Exception: continue
                sc = _score_english_simple(ptcand)
                delta = sc - cur_score
                elapsed = time.time()-start_sa
                T = T0 * (1 - elapsed / t_limit)
                if delta > 0 or random.random() < math.exp(delta / max(1e-6,T)):
                    cur_key, cur_score = cand, sc
            if cur_score > best_score:
                best_key, best_score = cur_key, cur_score
        out.append((best_key, len(best_key), best_score))
        if len(out) >= top or (time_limit and time.time()-start > time_limit):
            break
    return out

# -----------------------
# XOR helpers & repeating XOR refinement
# -----------------------
def _score_xor_plain_bytes(bts):
    try:
        s = bts.decode(errors='ignore')
        return _score_english_simple(s)
    except Exception:
        return -999.0

def _single_byte_score_tuple(k, data):
    pt = bytes(b ^ k for b in data)
    try: s = pt.decode('utf-8', errors='ignore')
    except Exception: s = pt.decode('latin1', errors='ignore')
    return (k, _score_english_simple(s), s)

def guess_single_byte_xor_from_hex(hex_text: str, top: int = 12, use_process=False, max_workers=4, progress_cb=None):
    try:
        data = bytes.fromhex(hex_text)
    except Exception:
        return []
    if not data: return []
    args = list(range(256)); results=[]
    mw = _clamp_workers(max_workers)
    executor_cls = concurrent.futures.ThreadPoolExecutor
    if use_process:
        try: executor_cls = concurrent.futures.ProcessPoolExecutor
        except Exception: executor_cls = concurrent.futures.ThreadPoolExecutor
    with executor_cls(max_workers=mw) as ex:
        futures = {ex.submit(_single_byte_score_tuple, k, data): k for k in args}
        for i, fut in enumerate(concurrent.futures.as_completed(futures)):
            res = fut.result()
            if res: results.append(res)
            if progress_cb: progress_cb(i+1, len(args))
    results.sort(key=lambda x: x[1], reverse=True)
    return results[:top]

def _hamming_distance(b1: bytes, b2: bytes) -> int:
    assert len(b1) == len(b2)
    return sum(bin(x ^ y).count('1') for x,y in zip(b1,b2))

def _repeating_key_worker_for_keylen(args):
    keylen, data = args
    key_bytes=[]
    for i in range(keylen):
        block = data[i::keylen]
        best_b=0; best_score = -1e9
        for b in range(256):
            pt = bytes(x ^ b for x in block)
            try:
                s = pt.decode('utf-8', errors='ignore')
            except Exception:
                s = pt.decode('latin1', errors='ignore')
            sc = _score_english_simple(s)
            if sc > best_score:
                best_score = sc; best_b=b
        key_bytes.append(best_b)
    key = bytes(key_bytes)
    pt = bytes(data[i] ^ key[i % len(key)] for i in range(len(data)))
    try: ptext = pt.decode('utf-8', errors='ignore')
    except Exception: ptext = pt.decode('latin1', errors='ignore')
    sc = _score_english_simple(ptext)
    return (key.hex(), sc, ptext)

def guess_repeating_xor_from_hex(hex_text: str, max_keylen: int = REPEAT_XOR_MAX, top: int = 6, use_process=False, max_workers=4, progress_cb=None, heavy=False, time_limit=None):
    try:
        data = bytes.fromhex(hex_text)
    except Exception:
        return []
    if not data: return []
    # estimate key sizes by normalized hamming
    key_sizes = []
    for keylen in range(1, min(max_keylen, len(data)) + 1):
        blocks = [data[i:i+keylen] for i in range(0, min(len(data), keylen*8), keylen)]
        if len(blocks) < 2: continue
        pairs=[]
        for i in range(len(blocks)-1):
            if len(blocks[i]) == len(blocks[i+1]):
                pairs.append(_hamming_distance(blocks[i], blocks[i+1]) / keylen)
        if pairs:
            key_sizes.append((sum(pairs)/len(pairs), keylen))
    key_sizes.sort()
    candidates = [k for _,k in key_sizes[:min(len(key_sizes), max(12, max_keylen))]]
    if not candidates:
        candidates = list(range(1, max_keylen+1))
    args = [(k, data) for k in candidates]
    results=[]
    mw = _clamp_workers(max_workers)
    executor_cls = concurrent.futures.ThreadPoolExecutor
    if use_process:
        try: executor_cls = concurrent.futures.ProcessPoolExecutor
        except Exception: executor_cls = concurrent.futures.ThreadPoolExecutor
    start = time.time()
    with executor_cls(max_workers=mw) as ex:
        futures = {ex.submit(_repeating_key_worker_for_keylen, arg): arg[0] for arg in args}
        for i, fut in enumerate(concurrent.futures.as_completed(futures)):
            if time_limit and (time.time()-start) > time_limit: break
            res = fut.result()
            if res: results.append(res)
            if progress_cb: progress_cb(len(results), len(args))
    # refinement: local hillclimb / SA if heavy
    refined=[]
    deadline = time.time() + (time_limit or (10.0 if heavy else 2.0))
    for keyhex, sc, pt in results:
        keyb = bytes.fromhex(keyhex)
        best_key = bytearray(keyb); best_score = sc
        if heavy:
            # SA time-limited
            sa_deadline = min(deadline, time.time()+ (time_limit or 20.0))
            cur_key = bytearray(best_key); cur_score = best_score
            T0 = 1.0
            while time.time() < sa_deadline:
                pos = random.randrange(len(cur_key))
                cand_key = bytearray(cur_key)
                cand_key[pos] = random.randrange(256)
                plain = bytes(data[i] ^ cand_key[i%len(cand_key)] for i in range(len(data)))
                s_plain = plain.decode('latin1', errors='ignore')
                sc2 = _score_english_simple(s_plain)
                delta = sc2 - cur_score
                tleft = max(1e-6, sa_deadline - time.time())
                T = T0 * (tleft / (time_limit or 20.0))
                if delta > 0 or random.random() < math.exp(delta / max(1e-6, T)):
                    cur_key, cur_score = cand_key, sc2
            if cur_score > best_score:
                best_key, best_score = cur_key, cur_score
        else:
            # small hillclimb quick pass
            iters = 0
            improved = True
            while improved and iters < 200 and time.time() < deadline:
                improved=False; iters+=1
                for pos in range(len(best_key)):
                    for candidate in range(256):
                        if best_key[pos] == candidate: continue
                        cand_key = bytearray(best_key)
                        cand_key[pos] = candidate
                        plain = bytes(data[i] ^ cand_key[i%len(cand_key)] for i in range(len(data)))
                        s_plain = plain.decode('latin1', errors='ignore')
                        sc2 = _score_english_simple(s_plain)
                        if sc2 > best_score:
                            best_key, best_score = cand_key, sc2; improved=True; break
                    if improved: break
        plain = bytes(data[i] ^ best_key[i%len(best_key)] for i in range(len(data)))
        refined.append((best_key.hex(), best_score, plain.decode('latin1', errors='replace')))
    refined.sort(key=lambda x: x[1], reverse=True)
    return refined[:top]

# -----------------------
# Smart / Chain helpers
# -----------------------
_re_b64 = re.compile(r'^[A-Za-z0-9+/=\s]+$')
_re_b64url = re.compile(r'^[A-Za-z0-9_\-=\s]+$')
_re_b32 = re.compile(r'^[A-Z2-7=\s]+$')
_re_hex = re.compile(r'^[0-9A-Fa-f\s]+$')
_re_bin = re.compile(r'^(?:[01]{8}\s+)*[01]{8}$')
_re_morse = re.compile(r'^[\.\-\/\s]+$')
_re_urlpct = re.compile(r'%[0-9A-Fa-f]{2}')
_re_bacon = re.compile(r'^[AaBb\s]+$')

def _score_keywords(text, keywords):
    t = (text or '').lower()
    return sum(1 for w in keywords if w in t)

def _decoder_variants_max(text, aggressive=True):
    out=[]
    pairs = [("Base64", base64_decrypt),("Base64 URL-safe", b64url_decode),("Base32", base32_decode),("Ascii85", a85_decode),
             ("URL-encoded", url_decode),("Hex", lambda s: hex_decrypt(s.replace(' ',''))),("Binary", binary_decrypt),
             ("Morse", morse_decode),("Baconian", bacon_decode),("Baconian (grouped)", bacon_decode_loose),
             ("Reverse", reverse_cipher),("Atbash", atbash_cipher),("ROT13", rot13),("ROT47", rot47)]
    for lab,fn in pairs:
        try:
            d = fn(text)
        except Exception:
            d = None
        if d and d!=text: out.append((lab,d))
    for s in range(26):
        d = caesar_decrypt(text, s)
        if d and d!=text: out.append((f"Caesar shift={s}", d))
    for r in range(2,11):
        try:
            d = rail_fence_decrypt(text, r)
            if d and d!=text: out.append((f"Rail r={r}", d))
        except Exception: pass
    for a in AFFINE_VALID_A:
        for b in range(26):
            try:
                d = affine_decrypt(text, a, b)
                if d and d!=text: out.append((f"Affine a={a},b={b}", d))
            except Exception: pass
    if aggressive:
        for key,klen,aic in guess_vigenere_keys(text, top=8):
            try:
                d = vigenere_decrypt(text, key)
                if d and d!=text: out.append((f"Vig guessed {key}", d))
            except Exception: pass
        for k in KEY_TRY_LIST[:60]:
            try:
                d = playfair_decrypt_preserve(text,k)
                if d and d!=text: out.append((f"Playfair {k}", d))
            except Exception: pass
    seen=set(); uniq=[]
    for lab,dec in out:
        if dec not in seen:
            seen.add(dec); uniq.append((lab,dec))
    return uniq

def smart_decrypt(encrypted_text, user_keywords):
    if isinstance(user_keywords, str):
        user_kw = [w.strip().lower() for w in user_keywords.split(',') if w.strip()]
    else:
        user_kw = list(user_keywords or [])
    keywords = list(dict.fromkeys(user_kw + KEYWORD_MATCH_LIST))
    def accept(dec): return dec and _score_keywords(dec, keywords) >= 1
    if _re_urlpct.search(encrypted_text):
        dec = url_decode(encrypted_text);
        if accept(dec): return dec, "URL"
    if _re_morse.match(encrypted_text.strip()):
        dec = morse_decode(encrypted_text);
        if accept(dec): return dec,"Morse"
    if _re_bacon.match(encrypted_text.strip()):
        dec = bacon_decode(encrypted_text);
        if accept(dec): return dec,"Baconian"
    dec = bacon_decode_loose(encrypted_text)
    if accept(dec): return dec, "Baconian (grouped)"
    if _re_bin.match(encrypted_text.strip()):
        dec = binary_decrypt(encrypted_text)
        if accept(dec): return dec, "Binary (8-bit)"
    if _re_hex.match(encrypted_text.replace(' ','').strip()) and len(encrypted_text.replace(' ',''))%2==0:
        dec = hex_decrypt(encrypted_text.replace(' ',''))
        if accept(dec): return dec, "Hex"
    dec = a85_decode(encrypted_text)
    if accept(dec): return dec, "Ascii85"
    if _re_b64.match(encrypted_text.strip()):
        dec = base64_decrypt(encrypted_text)
        if accept(dec): return dec, "Base64"
    if _re_b64url.match(encrypted_text.strip()):
        dec = b64url_decode(encrypted_text)
        if accept(dec): return dec, "Base64 URL-safe"
    if _re_b32.match(encrypted_text.strip()):
        dec = base32_decode(encrypted_text)
        if accept(dec): return dec, "Base32"
    best=(0,None,None)
    for s in range(26):
        dec = caesar_decrypt(encrypted_text, s)
        hits = _score_keywords(dec, keywords)
        if hits > best[0]: best=(hits,dec,f"Caesar shift={s}")
    if best[0] >= 1: return best[1], best[2]
    for name, fn in [("ROT13",rot13),("ROT47",rot47),("Reverse",reverse_cipher),("Atbash",atbash_cipher)]:
        dec = fn(encrypted_text)
        if accept(dec): return dec, name
    for r in range(2,11):
        try:
            dec = rail_fence_decrypt(encrypted_text, r)
            if accept(dec): return dec, f"Rail Fence r={r}"
        except Exception: pass
    for a in AFFINE_VALID_A:
        for b in range(26):
            try:
                dec=affine_decrypt(encrypted_text,a,b)
                if accept(dec): return dec, f"Affine a={a},b={b}"
            except Exception: pass
    for key,klen,aic in guess_vigenere_keys(encrypted_text, top=12):
        try:
            dec = vigenere_decrypt(encrypted_text, key)
            if accept(dec): return dec, f"Vigenere guessed '{key}'"
        except Exception: pass
    for key in KEY_TRY_LIST:
        try:
            dec = vigenere_decrypt(encrypted_text, key)
            if accept(dec): return dec, f"Vigenere key='{key}'"
        except Exception: pass
    stext = encrypted_text.replace(' ','')
    if _re_hex.match(stext) and len(stext)%2==0:
        for k,score,pt in guess_single_byte_xor_from_hex(stext, top=8, use_process=USE_PROCESS_POOL_DEFAULT, max_workers=MAX_WORKERS_DEFAULT):
            if accept(pt): return pt, f"SingleByteXOR 0x{k:02x}"
        for keyhex,score,pt in guess_repeating_xor_from_hex(stext, max_keylen=REPEAT_XOR_MAX, top=6, use_process=USE_PROCESS_POOL_DEFAULT, max_workers=MAX_WORKERS_DEFAULT):
            if accept(pt): return pt, f"RepeatingXOR keyhex={keyhex}"
        for k in KEY_TRY_LIST[:80]:
            try:
                d = xor_decrypt_from_hex(stext, k)
                if accept(d): return d, f"XOR(hex) key={k}"
            except Exception: pass
    for key in KEY_TRY_LIST[:80]:
        for fn,label in [(autokey_decrypt,"Autokey"),(beaufort,"Beaufort"),(porta,"Porta"),(playfair_decrypt_preserve,"Playfair")]:
            try:
                d = fn(encrypted_text, key)
                if accept(d): return d, f"{label} key={key}"
            except Exception: pass
    return None, "No match found"

# -----------------------
# Improved "other keys" guesser
# -----------------------
def guess_other_keys_improved(encrypted_text, max_vig=20, xor_top=12, repeat_xor_top=8, use_process=USE_PROCESS_POOL_DEFAULT, max_workers=MAX_WORKERS_DEFAULT, heavy=False, heavy_time_limit=60, progress_cb=None):
    results=[]
    seen=set()
    text = encrypted_text.strip()
    # vigenere candidates and refinement
    vguesses = guess_vigenere_keys(text, max_len=24, top=max_vig, heavy=heavy, time_limit=(heavy_time_limit if heavy else 8))
    if progress_cb: progress_cb("vigenere", 1.0)
    for key,klen,score_est in vguesses:
        try:
            pt = vigenere_decrypt(text, key)
            sc = _score_english_simple(pt)
            if pt not in seen:
                seen.add(pt); results.append((f"Vigenere key={key}", sc, pt))
        except Exception:
            pass
    # seeded keys try for Autokey/Beaufort/Porta/Playfair
    keys_to_try = list(dict.fromkeys([k for k,_a,_b in vguesses] + KEY_TRY_LIST + [k for k in KEYWORD_MATCH_LIST if len(k)>=3]))
    if progress_cb: progress_cb("seeded", 0.0)
    for i,k in enumerate(keys_to_try[:200]):
        if progress_cb: progress_cb("seeded", (i+1)/min(len(keys_to_try[:200]),200))
        for fn,label in [(autokey_decrypt,"Autokey"),(beaufort,"Beaufort"),(porta,"Porta")]:
            try:
                pt = fn(text, k)
                sc = _score_english_simple(pt)
                if pt not in seen:
                    seen.add(pt); results.append((f"{label} key={k}", sc, pt))
            except Exception:
                pass
        # Playfair preserve
        if any(ch.isalpha() for ch in text):
            try:
                pt = playfair_decrypt_preserve(text, k)
                sc = _score_english_simple(pt)
                if pt not in seen:
                    seen.add(pt); results.append((f"Playfair key={k}", sc, pt))
            except Exception:
                pass
    # XOR attempts if looks like hex
    stext = text.replace(' ', '')
    if re.fullmatch(r'^[0-9A-Fa-f]+$', stext) and len(stext) % 2 == 0:
        if progress_cb: progress_cb("xor_single", 0.0)
        try:
            sb = guess_single_byte_xor_from_hex(stext, top=xor_top, use_process=use_process, max_workers=max_workers, progress_cb=None)
            for i,(k,sc,pt) in enumerate(sb):
                if pt not in seen:
                    seen.add(pt); results.append((f"SingleXOR 0x{k:02x}", sc, pt))
            if progress_cb: progress_cb("xor_single", 1.0)
        except Exception:
            pass
        # repeating key with possible heavy refinement/timebox
        if progress_cb: progress_cb("xor_repeat", 0.0)
        try:
            rx = guess_repeating_xor_from_hex(stext, max_keylen=(REPEAT_XOR_MAX if not heavy else max(REPEAT_XOR_MAX, 32)), top=repeat_xor_top, use_process=use_process, max_workers=max_workers, progress_cb=None, heavy=heavy, time_limit=(heavy_time_limit if heavy else 8))
            for i,(keyhex,sc,pt) in enumerate(rx):
                if pt not in seen:
                    seen.add(pt); results.append((f"RepeatingXOR keyhex={keyhex}", sc, pt))
            if progress_cb: progress_cb("xor_repeat", 1.0)
        except Exception:
            pass
    results.sort(key=lambda x: x[1], reverse=True)
    return results

# -----------------------
# GUI
# -----------------------
class EncryptorApp:
    def __init__(self, root):
        self.root = root
        root.title("Encryptor & Decryptor — improved guessers")
        root.geometry("1100x820"); root.minsize(900,620)
        self.stop_event = threading.Event()
        self.use_process_pool = USE_PROCESS_POOL_DEFAULT
        self.max_workers = MAX_WORKERS_DEFAULT
        self.dark_mode = False
        self.heavy_mode = tk.BooleanVar(value=False)
        self._text_widgets = []
        self._build_ui()
        self._apply_theme()

    def _build_ui(self):
        nb = ttk.Notebook(self.root); nb.pack(fill='both', expand=True)
        self.tabs={}
        for name in ("Encrypt","Decrypt","Smart","Tests","Settings"):
            f=ttk.Frame(nb); nb.add(f, text=name); self.tabs[name]=f
        self._build_encrypt(self.tabs["Encrypt"])
        self._build_decrypt(self.tabs["Decrypt"])
        self._build_smart(self.tabs["Smart"])
        self._build_tests(self.tabs["Tests"])
        self._build_settings(self.tabs["Settings"])

    def _text_with_scroll(self, parent, height=8):
        fr = ttk.Frame(parent)
        txt = tk.Text(fr, height=height, wrap='none', undo=True)
        v = ttk.Scrollbar(fr, orient='vertical', command=txt.yview)
        h = ttk.Scrollbar(fr, orient='horizontal', command=txt.xview)
        txt.configure(yscrollcommand=v.set, xscrollcommand=h.set)
        txt.grid(row=0, column=0, sticky='nsew')
        v.grid(row=0, column=1, sticky='ns')
        h.grid(row=1, column=0, sticky='ew')
        fr.columnconfigure(0, weight=1); fr.rowconfigure(0, weight=1)
        self._text_widgets.append(txt)
        return fr, txt

    def _build_encrypt(self, tab):
        tk.Label(tab, text="Input:").pack(anchor='w', padx=6)
        fr, self.encrypt_input = self._text_with_scroll(tab, height=6); fr.pack(fill='both', padx=6, pady=4)
        ctrl = ttk.Frame(tab); ctrl.pack(fill='x', padx=6)
        ttk.Label(ctrl, text="Mode:").grid(row=0,column=0)
        self.encrypt_mode = ttk.Combobox(ctrl, values=self._modes(), state='readonly', width=36); self.encrypt_mode.current(0); self.encrypt_mode.grid(row=0,column=1,padx=6)
        ttk.Label(ctrl, text="Shift:").grid(row=0,column=2)
        self.encrypt_shift = tk.Entry(ctrl, width=6); self.encrypt_shift.insert(0,"3"); self.encrypt_shift.grid(row=0,column=3,padx=6)
        ttk.Label(ctrl, text="Key/Params:").grid(row=1,column=0)
        self.encrypt_key = tk.Entry(ctrl, width=64); self.encrypt_key.grid(row=1,column=1,columnspan=3,padx=6,pady=4)
        ttk.Button(ctrl, text="Encrypt", command=self.encrypt_message).grid(row=0,column=4,padx=6)
        ttk.Button(ctrl, text="Load…", command=lambda: self._load_into(self.encrypt_input)).grid(row=1,column=4,padx=6)
        tk.Label(tab, text="Result:").pack(anchor='w', padx=6)
        fr2, self.encrypt_output = self._text_with_scroll(tab, height=10); fr2.pack(fill='both', expand=True, padx=6, pady=4)

    def _build_decrypt(self, tab):
        tk.Label(tab, text="Input:").pack(anchor='w', padx=6)
        fr, self.decrypt_input = self._text_with_scroll(tab, height=6); fr.pack(fill='both', padx=6, pady=4)
        ctrl = ttk.Frame(tab); ctrl.pack(fill='x', padx=6)
        ttk.Label(ctrl, text="Mode:").grid(row=0,column=0)
        self.decrypt_mode = ttk.Combobox(ctrl, values=self._modes(), state='readonly', width=36); self.decrypt_mode.current(0); self.decrypt_mode.grid(row=0,column=1,padx=6)
        ttk.Label(ctrl, text="Shift:").grid(row=0,column=2)
        self.decrypt_shift = tk.Entry(ctrl, width=6); self.decrypt_shift.insert(0,"3"); self.decrypt_shift.grid(row=0,column=3,padx=6)
        ttk.Label(ctrl, text="Key/Params:").grid(row=1,column=0)
        self.decrypt_key = tk.Entry(ctrl, width=64); self.decrypt_key.grid(row=1,column=1,columnspan=3,padx=6,pady=4)
        ttk.Button(ctrl, text="Decrypt", command=self.decrypt_message).grid(row=0,column=4,padx=6)
        ttk.Button(ctrl, text="Load…", command=lambda: self._load_into(self.decrypt_input)).grid(row=1,column=4,padx=6)
        tk.Label(tab, text="Result:").pack(anchor='w', padx=6)
        fr2, self.decrypt_output = self._text_with_scroll(tab, height=10); fr2.pack(fill='both', expand=True, padx=6, pady=4)

    def _build_smart(self, tab):
        tk.Label(tab, text="Encrypted message:").pack(anchor='w', padx=6)
        fr, self.smart_input = self._text_with_scroll(tab, height=6); fr.pack(fill='both', padx=6, pady=4)
        kf = ttk.Frame(tab); kf.pack(fill='x', padx=6)
        ttk.Label(kf, text="Expected keywords:").grid(row=0,column=0, sticky='w')
        self.keyword_entry = tk.Entry(kf, width=80); self.keyword_entry.insert(0,"password, access, secret"); self.keyword_entry.grid(row=0,column=1,padx=6)
        bf = ttk.Frame(tab); bf.pack(fill='x', padx=6, pady=6)
        ttk.Button(bf, text="Smart Decrypt", command=self.handle_smart_decrypt).pack(side='left', padx=6)
        ttk.Button(bf, text="Brute Force All", command=self.brute_force_all).pack(side='left', padx=6)
        ttk.Button(bf, text="Guess XOR Keys (quick)", command=self.guess_xor_from_ui).pack(side='left', padx=6)
        ttk.Button(bf, text="XOR Guess Test (thorough)", command=self.xor_guess_test).pack(side='left', padx=6)
        ttk.Button(bf, text="Guess Other Keys (improved)", command=self.guess_other_keys_from_ui).pack(side='left', padx=6)
        ttk.Label(tab, text="Chain Decrypt (BFS):").pack(anchor='w', padx=6)
        chainf = ttk.Frame(tab); chainf.pack(fill='x', padx=6)
        ttk.Label(chainf, text="Depth:").grid(row=0,column=0); self.chain_depth = tk.Spinbox(chainf, from_=1,to=6,width=4); self.chain_depth.delete(0,tk.END); self.chain_depth.insert(0,"3"); self.chain_depth.grid(row=0,column=1,padx=4)
        ttk.Label(chainf, text="Min hits:").grid(row=0,column=2); self.chain_hits = tk.Spinbox(chainf, from_=1,to=6,width=4); self.chain_hits.delete(0,tk.END); self.chain_hits.insert(0,"1"); self.chain_hits.grid(row=0,column=3,padx=4)
        ttk.Label(chainf, text="Max nodes:").grid(row=0,column=4); self.chain_nodes = tk.Spinbox(chainf, from_=200,to=20000,increment=100,width=8); self.chain_nodes.delete(0,tk.END); self.chain_nodes.insert(0,"4000"); self.chain_nodes.grid(row=0,column=5,padx=4)
        self.aggressive_var = tk.IntVar(value=1); ttk.Checkbutton(chainf, text="Aggressive", variable=self.aggressive_var).grid(row=0,column=6,padx=8)
        ttk.Button(chainf, text="Run Chain Decrypt", command=self.handle_chain_decrypt).grid(row=0,column=7,padx=6)
        ttk.Button(chainf, text="Stop", command=self._stop).grid(row=0,column=8,padx=6)
        self.chain_progress = ttk.Progressbar(chainf, orient='horizontal', length=200, mode='determinate')
        self.chain_progress.grid(row=1, column=0, columnspan=4, pady=4, sticky='w')
        ttk.Label(tab, text="Vigenere Key Guesser:").pack(anchor='w', padx=6, pady=(8,0))
        vigf = ttk.Frame(tab); vigf.pack(fill='x', padx=6)
        ttk.Button(vigf, text="Guess Vigenere Keys", command=self.handle_vigenere_guess).pack(side='left', padx=6)
        ttk.Label(tab, text="Results:").pack(anchor='w', padx=6)
        fr2, self.smart_output = self._text_with_scroll(tab, height=14); fr2.pack(fill='both', expand=True, padx=6, pady=4)
        xorf = ttk.Frame(tab); xorf.pack(fill='x', padx=6)
        self.xor_progress = ttk.Progressbar(xorf, orient='horizontal', length=300, mode='determinate'); self.xor_progress.pack(side='left', padx=6)

    def _build_tests(self, tab):
        ctrl = ttk.Frame(tab); ctrl.pack(fill='x', padx=6, pady=6)
        ttk.Button(ctrl, text="Run Quick Tests", command=self.run_tests).pack(side='left', padx=6)
        ttk.Button(ctrl, text="Stop", command=self._stop).pack(side='left', padx=6)
        ttk.Button(ctrl, text="Clear", command=lambda: self._set_text(self.tests_output, "")).pack(side='left', padx=6)
        fr, self.tests_output = self._text_with_scroll(tab, height=28); fr.pack(fill='both', expand=True, padx=6, pady=4)

    def _build_settings(self, tab):
        global REPEAT_XOR_MAX
        ttk.Label(tab, text="Settings").pack(anchor='w', padx=6, pady=6)
        self.proc_var = tk.IntVar(value=1 if USE_PROCESS_POOL_DEFAULT else 0)
        ttk.Checkbutton(tab, text="Use process pool for heavy tasks (CPU-bound)", variable=self.proc_var).pack(anchor='w', padx=8)
        self.dark_var = tk.IntVar(value=1 if self.dark_mode else 0)
        ttk.Checkbutton(tab, text="Dark mode", variable=self.dark_var, command=self._apply_theme).pack(anchor='w', padx=8)
        ttk.Checkbutton(tab, text="Heavy Duty (enable heavier searches/SA)", variable=self.heavy_mode).pack(anchor='w', padx=8)
        ttk.Label(tab, text="Max workers:").pack(anchor='w', padx=8)
        self.workers_spin = tk.Spinbox(tab, from_=1,to=256,width=6)
        self.workers_spin.delete(0,tk.END); self.workers_spin.insert(0,str(MAX_WORKERS_DEFAULT)); self.workers_spin.pack(anchor='w', padx=12)
        ttk.Label(tab, text="Repeat-XOR max key length:").pack(anchor='w', padx=8, pady=(8,0))
        self.repeat_spin = tk.Spinbox(tab, from_=2,to=128,width=6); self.repeat_spin.delete(0,tk.END); self.repeat_spin.insert(0,str(REPEAT_XOR_MAX)); self.repeat_spin.pack(anchor='w', padx=12)
        ttk.Button(tab, text="Apply Settings", command=self.apply_settings).pack(anchor='w', padx=8, pady=6)

    def _modes(self):
        return [
            'Caesar Cipher','Reverse Cipher','ROT13','ROT47','Atbash Cipher','Base64','Base64 URL-safe','Base32',
            'Ascii85','URL','Hex Encoding','Binary Encoding','Leetspeak','Vigenère','Vigenère Autokey','Running Key',
            'Beaufort','Porta','XOR (hex out)','Rail Fence','Affine','Playfair','Playfair (preserve layout)',
            'Columnar Transposition','Morse','Baconian'
        ]

    # ---------- Handlers ----------
    def encrypt_message(self):
        message = self.encrypt_input.get("1.0", tk.END).rstrip('\n')
        mode = self.encrypt_mode.get(); key = self.encrypt_key.get()
        try: shift = int(self.encrypt_shift.get())
        except Exception: shift = 3
        try:
            if mode == 'Caesar Cipher': out = caesar_cipher(message, shift)
            elif mode == 'Reverse Cipher': out = reverse_cipher(message)
            elif mode == 'ROT13': out = rot13(message)
            elif mode == 'ROT47': out = rot47(message)
            elif mode == 'Atbash Cipher': out = atbash_cipher(message)
            elif mode == 'Base64': out = base64.b64encode(message.encode()).decode()
            elif mode == 'Base64 URL-safe': out = b64url_encode(message)
            elif mode == 'Base32': out = base32_encode(message)
            elif mode == 'Ascii85': out = a85_encode(message)
            elif mode == 'URL': out = url_encode(message)
            elif mode == 'Hex Encoding': out = message.encode().hex()
            elif mode == 'Binary Encoding': out = ' '.join(format(ord(c),'08b') for c in message)
            elif mode == 'Leetspeak':
                m={'A':'4','a':'4','B':'8','b':'8','E':'3','e':'3','G':'6','g':'6','I':'1','i':'1','O':'0','o':'0','S':'5','s':'5','T':'7','t':'7','Z':'2','z':'2'}
                out=''.join(m.get(c,c) for c in message)
            elif mode == 'Vigenère': out = vigenere_encrypt(message, key)
            elif mode == 'Vigenère Autokey': out = autokey_encrypt(message, key)
            elif mode == 'Running Key': out = runningkey_encrypt(message, key)
            elif mode == 'Beaufort': out = beaufort(message, key)
            elif mode == 'Porta': out = porta(message, key)
            elif mode == 'XOR (hex out)': out = xor_encrypt_to_hex(message, key)
            elif mode == 'Rail Fence': out = rail_fence_encrypt(message, int(key))
            elif mode == 'Affine': a,b = map(int, key.split(',')); out = affine_encrypt(message, a, b)
            elif mode == 'Playfair': out = playfair_encrypt_letters_only(message, key)
            elif mode == 'Playfair (preserve layout)': out = playfair_encrypt_preserve(message, key)
            elif mode == 'Columnar Transposition': out = columnar_encrypt(message, key)
            elif mode == 'Morse': out = morse_encode(message)
            elif mode == 'Baconian': out = bacon_encode(message)
            else: out = "[Invalid Mode]"
        except Exception as e:
            out = f"[Error] {e}"
        self._update_text(self.encrypt_output, out)

    def decrypt_message(self):
        message = self.decrypt_input.get("1.0", tk.END).rstrip('\n')
        mode = self.decrypt_mode.get(); key = self.decrypt_key.get()
        try: shift = int(self.decrypt_shift.get())
        except Exception: shift = 3
        try:
            if mode == 'Caesar Cipher': out = caesar_decrypt(message, shift)
            elif mode == 'Reverse Cipher': out = reverse_cipher(message)
            elif mode == 'ROT13': out = rot13(message)
            elif mode == 'ROT47': out = rot47(message)
            elif mode == 'Atbash Cipher': out = atbash_cipher(message)
            elif mode == 'Base64': out = base64_decrypt(message) or "[Invalid Base64]"
            elif mode == 'Base64 URL-safe': out = b64url_decode(message) or "[Invalid Base64 URL-safe]"
            elif mode == 'Base32': out = base32_decode(message) or "[Invalid Base32]"
            elif mode == 'Ascii85': out = a85_decode(message) or "[Invalid Ascii85]"
            elif mode == 'URL': out = url_decode(message) or "[Invalid URL]"
            elif mode == 'Hex Encoding': out = hex_decrypt(message.replace(' ','')) or "[Invalid Hex]"
            elif mode == 'Binary Encoding': out = binary_decrypt(message) or "[Invalid Binary]"
            elif mode == 'Leetspeak': out = "[Not reversible]"
            elif mode == 'Vigenère': out = vigenere_decrypt(message, key)
            elif mode == 'Vigenère Autokey': out = autokey_decrypt(message, key)
            elif mode == 'Running Key': out = runningkey_decrypt(message, key)
            elif mode == 'Beaufort': out = beaufort(message, key)
            elif mode == 'Porta': out = porta(message, key)
            elif mode == 'XOR (hex out)': out = xor_decrypt_from_hex(message.replace(' ',''), key) or "[Invalid Hex or Key]"
            elif mode == 'Rail Fence': out = rail_fence_decrypt(message, int(key))
            elif mode == 'Affine': a,b = map(int, key.split(',')); out = affine_decrypt(message, a, b)
            elif mode == 'Playfair': out = playfair_decrypt_letters_only(message, key)
            elif mode == 'Playfair (preserve layout)': out = playfair_decrypt_preserve(message, key)
            elif mode == 'Columnar Transposition': out = columnar_decrypt(message, key)
            elif mode == 'Morse': out = morse_decode(message) or "[Invalid Morse]"
            elif mode == 'Baconian': out = bacon_decode(message)
            else: out = "[Invalid Mode]"
        except Exception as e:
            out = f"[Error] {e}"
        self._update_text(self.decrypt_output, out)

    # Smart actions
    def handle_smart_decrypt(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc: messagebox.showwarning("Input","Enter encrypted text"); return
        dec, method = smart_decrypt(enc, self.keyword_entry.get())
        if dec:
            self._update_text(self.smart_output, dec + f"\n\n[Method: {method}]")
        else:
            self._update_text(self.smart_output, f"[No match] {method}")

    def brute_force_all(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc: messagebox.showwarning("Input","Enter encrypted text"); return
        keywords = [w.strip().lower() for w in self.keyword_entry.get().split(',') if w.strip()]
        search_terms = list(dict.fromkeys(keywords + KEYWORD_MATCH_LIST))
        results=[]
        def maybe_add(name, text):
            if not text: return
            hits = _score_keywords(text, search_terms)
            if hits >= 1: results.append((f"{name} (hits={hits})", text))
        for s in range(26): maybe_add(f"Caesar shift={s}", caesar_decrypt(enc, s))
        maybe_add("ROT13", rot13(enc)); maybe_add("ROT47", rot47(enc)); maybe_add("Reverse", reverse_cipher(enc)); maybe_add("Atbash", atbash_cipher(enc))
        for name,fn in [("Base64",base64_decrypt),("Base64 URL-safe",b64url_decode),("Base32",base32_decode),("Ascii85",a85_decode),("Hex",lambda s: hex_decrypt(s.replace(' ',''))),("Binary",binary_decrypt),("Morse",morse_decode),("URL-encoded",url_decode),("Baconian (spaced)",bacon_decode),("Baconian (grouped)",bacon_decode_loose)]:
            try: maybe_add(name, fn(enc))
            except Exception: pass
        for r in range(2,11):
            try: maybe_add(f"Rail Fence r={r}", rail_fence_decrypt(enc,r))
            except Exception: pass
        for a in AFFINE_VALID_A:
            for b in range(26):
                try: maybe_add(f"Affine a={a},b={b}", affine_decrypt(enc,a,b))
                except Exception: pass
        for key,klen,aic in guess_vigenere_keys(enc, top=8):
            try: maybe_add(f"Vigenere guessed {key}", vigenere_decrypt(enc,key))
            except Exception: pass
        for key in KEY_TRY_LIST:
            try: maybe_add(f"Vigenere key={key}", vigenere_decrypt(enc,key))
            except Exception: pass
            try: maybe_add(f"Autokey key={key}", autokey_decrypt(enc,key))
            except Exception: pass
            try: maybe_add(f"Beaufort key={key}", beaufort(enc,key))
            except Exception: pass
            try: maybe_add(f"Porta key={key}", porta(enc,key))
            except Exception: pass
            try: maybe_add(f"Playfair key={key}", playfair_decrypt_preserve(enc,key))
            except Exception: pass
        stext = enc.replace(' ','')
        if re.fullmatch(r'^[0-9A-Fa-f]+$', stext) and len(stext)%2==0:
            for k in KEY_TRY_LIST[:80]:
                try: maybe_add(f"XOR(hex) key={k}", xor_decrypt_from_hex(stext,k))
                except Exception: pass
            for k,score,pt in guess_single_byte_xor_from_hex(stext, top=6, use_process=self.use_process_pool, max_workers=self.max_workers):
                maybe_add(f"SingleByteXOR 0x{k:02x}", pt)
            for keyhex,score,pt in guess_repeating_xor_from_hex(stext, max_keylen=REPEAT_XOR_MAX, top=6, use_process=self.use_process_pool, max_workers=self.max_workers):
                maybe_add(f"RepeatingXOR keyhex={keyhex}", pt)
        if results:
            self._update_text(self.smart_output, "\n\n".join(f"[{m}]\n{t}" for m,t in results))
        else:
            self._update_text(self.smart_output, "[No matches found]")

    def guess_xor_from_ui(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc: messagebox.showwarning("Input","Enter encrypted text"); return
        stext = enc.replace(' ','')
        if not (re.fullmatch(r'^[0-9A-Fa-f]+$', stext) and len(stext)%2==0):
            messagebox.showinfo("XOR Guess", "Input doesn't look like hex bytes. Single-byte & repeating-key guessers expect hex input.")
            return
        self._update_text(self.smart_output, "Running quick XOR guesses...")
        self.xor_progress['mode'] = 'indeterminate'; self.xor_progress.start(20)
        def worker():
            try:
                sb = guess_single_byte_xor_from_hex(stext, top=12, use_process=self.use_process_pool, max_workers=self.max_workers, progress_cb=None)
                lines=[]
                if sb:
                    lines.append("== Single-byte XOR candidates ==")
                    for k,score,pt in sb: lines.append(f"key=0x{k:02x} score={score:.3f}\n{pt}\n")
                rx = guess_repeating_xor_from_hex(stext, max_keylen=REPEAT_XOR_MAX, top=8, use_process=self.use_process_pool, max_workers=self.max_workers)
                if rx:
                    lines.append("== Repeating-key XOR candidates ==")
                    for keyhex,score,pt in rx: lines.append(f"keyhex={keyhex} score={score:.3f}\n{pt}\n")
                tried=[]
                for k in KEY_TRY_LIST[:60]:
                    try:
                        d = xor_decrypt_from_hex(stext, k)
                        if d: tried.append((k, _score_keywords(d, KEYWORD_MATCH_LIST), d))
                    except Exception: pass
                tried.sort(key=lambda x: x[1], reverse=True)
                if tried:
                    lines.append("== XOR with common keys ==")
                    for k,sc,d in tried[:12]:
                        lines.append(f"key={k} hits={sc}\n{d}\n")
                if not lines: lines=["[No XOR candidates found]"]
                self._update_text(self.smart_output, "\n\n".join(lines))
            finally:
                try: self.xor_progress.stop()
                except Exception: pass
                self.xor_progress['mode']='determinate'; self.xor_progress['value']=0
        t=threading.Thread(target=worker); t.daemon=True; t.start()

    def xor_guess_test(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc: messagebox.showwarning("Input","Enter encrypted text"); return
        stext = enc.replace(' ','')
        if not (re.fullmatch(r'^[0-9A-Fa-f]+$', stext) and len(stext)%2==0):
            messagebox.showinfo("XOR Guess Test", "Input must be hex bytes (no spaces) for thorough XOR testing.")
            return
        self._update_text(self.smart_output, "Starting thorough XOR guess test...")
        self.xor_progress['mode']='determinate'; self.xor_progress['maximum']=100; self.xor_progress['value']=0
        def worker():
            try:
                start=time.time(); lines=[]
                lines.append("== Single-byte XOR top candidates ==")
                sb = guess_single_byte_xor_from_hex(stext, top=50, use_process=self.use_process_pool, max_workers=self.max_workers, progress_cb=lambda a,b: self._set_progress_fraction(self.xor_progress, a/b))
                for k,score,pt in sb:
                    lines.append(f"key=0x{k:02x} score={score:.4f}\n{pt[:500]}\n")
                self.xor_progress['mode']='indeterminate'; self.xor_progress.start(15)
                rx = guess_repeating_xor_from_hex(stext, max_keylen=(REPEAT_XOR_MAX if not self.heavy_mode.get() else max(REPEAT_XOR_MAX, 32)), top=20, use_process=self.use_process_pool, max_workers=self.max_workers, heavy=self.heavy_mode.get(), time_limit=(60 if self.heavy_mode.get() else 8))
                self.xor_progress.stop(); self.xor_progress['mode']='determinate'; self.xor_progress['value']=60
                lines.append("\n== Repeating-key XOR candidates (thorough) ==")
                for keyhex,score,pt in rx:
                    lines.append(f"keyhex={keyhex} score={score:.4f}\n{pt[:500]}\n")
                lines.append("\n== Try textual keys from list ==")
                tried=[]
                for k in KEY_TRY_LIST[:200]:
                    try:
                        d = xor_decrypt_from_hex(stext, k)
                        if d:
                            sc = _score_keywords(d, KEYWORD_MATCH_LIST)
                            tried.append((k, sc, d[:400]))
                    except Exception: pass
                tried.sort(key=lambda x: x[1], reverse=True)
                for k,sc,d in tried[:40]:
                    lines.append(f"key={k} hits={sc}\n{d}\n")
                duration=time.time()-start
                lines.append(f"\nFinished thorough XOR guess test in {duration:.1f}s")
                self._update_text(self.smart_output, "\n\n".join(lines))
            finally:
                try: self.xor_progress.stop()
                except Exception: pass
                self.xor_progress['mode']='determinate'; self.xor_progress['value']=0
        t=threading.Thread(target=worker); t.daemon=True; t.start()

    # Improved Other Keys button
    def guess_other_keys_from_ui(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc:
            messagebox.showwarning("Input","Please enter an encrypted message.")
            return
        self._update_text(self.smart_output, "Running improved other-keys guesser (this may take a little while)...")
        self.xor_progress['mode']='indeterminate'; self.xor_progress.start(18)
        use_process = bool(self.proc_var.get()) if hasattr(self,'proc_var') else self.use_process_pool
        maxw = int(self.workers_spin.get()) if hasattr(self,'workers_spin') else self.max_workers
        heavy = bool(self.heavy_mode.get())
        time_limit = 60 if heavy else 8
        def progress_cb(stage, frac):
            # stage can be string; we don't update precise progress but could
            pass
        def worker():
            try:
                candidates = guess_other_keys_improved(enc, max_vig=24, xor_top=20, repeat_xor_top=12, use_process=use_process, max_workers=maxw, heavy=heavy, heavy_time_limit=time_limit, progress_cb=progress_cb)
                if not candidates:
                    self._update_text(self.smart_output, "[No candidates found]")
                    return
                lines=["Top candidates (sorted by english score):\n"]
                for method,score,pt in candidates[:60]:
                    preview = pt[:600].replace('\n',' ')
                    lines.append(f"[{method}] score={score:.3f}\n{preview}\n")
                self._update_text(self.smart_output, "\n".join(lines))
            finally:
                try: self.xor_progress.stop()
                except Exception: pass
                self.xor_progress['mode']='determinate'; self.xor_progress['value']=0
        t=threading.Thread(target=worker); t.daemon=True; t.start()

    # Chain decrypt
    def handle_chain_decrypt(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc: messagebox.showwarning("Input","Enter encrypted text"); return
        try: depth = int(self.chain_depth.get())
        except: depth = 3
        try: hits = int(self.chain_hits.get())
        except: hits = 1
        try: max_nodes = int(self.chain_nodes.get())
        except: max_nodes = 4000
        aggressive = bool(self.aggressive_var.get())
        self.stop_event.clear()
        self.chain_progress['value']=0; self.chain_progress['maximum']=max_nodes
        t=threading.Thread(target=self._chain_worker, args=(enc,hits,depth,max_nodes,aggressive)); t.daemon=True; t.start()

    def _chain_worker(self, enc, hits, depth, max_nodes, aggressive):
        self._update_text(self.smart_output, "Running chain decrypt...")
        def progress_cb(nodes, total):
            try: self.chain_progress['value'] = nodes
            except Exception: pass
        result, path, nodes = self._chain_bfs_simple(enc, self.keyword_entry.get(), min_hits=hits, max_depth=depth, max_nodes=max_nodes, aggressive=aggressive, stop_event=self.stop_event, progress_cb=progress_cb)
        if result:
            self._update_text(self.smart_output, result + "\n\n[Path] " + path + f"\n[Visited nodes] {nodes}")
        else:
            self._update_text(self.smart_output, f"[No layered match] {path}\n[Visited nodes] {nodes}")
        self.chain_progress['value'] = 0

    def _chain_bfs_simple(self, encrypted_text, user_keywords, min_hits=1, max_depth=3, max_nodes=4000, aggressive=True, stop_event: threading.Event=None, progress_cb=None):
        if isinstance(user_keywords, str):
            user_kw = [w.strip().lower() for w in user_keywords.split(',') if w.strip()]
        else:
            user_kw = list(user_keywords or [])
        keywords = list(dict.fromkeys(user_kw + KEYWORD_MATCH_LIST))
        def hits_of(s): return _score_keywords(s, keywords)
        visited=set([encrypted_text]); q=deque(); q.append((encrypted_text, [], 0)); nodes=0
        if hits_of(encrypted_text) >= min_hits: return encrypted_text, "[start plain]", 1
        while q and nodes < max_nodes:
            if stop_event and stop_event.is_set(): return None, "Stopped by user", nodes
            s, path, depth = q.popleft(); nodes += 1
            if progress_cb and nodes%50==0: progress_cb(nodes, max_nodes)
            if depth >= max_depth: continue
            variants = _decoder_variants_max(s, aggressive=aggressive)
            random.shuffle(variants)
            for lab, nxt in variants:
                if nxt in visited: continue
                visited.add(nxt)
                if hits_of(nxt) >= min_hits:
                    return nxt, " -> ".join(path + [lab]), nodes
                q.append((nxt, path + [lab], depth+1))
        return None, f"No layered match up to depth {max_depth}", nodes

    def handle_vigenere_guess(self):
        enc = self.smart_input.get("1.0", tk.END).strip()
        if not enc: messagebox.showwarning("Input","Enter encrypted text"); return
        heavy = bool(self.heavy_mode.get())
        guesses = guess_vigenere_keys(enc, top=20, heavy=heavy, time_limit=(60 if heavy else 8))
        if not guesses:
            self._update_text(self.smart_output, "No strong Vigenere signals found.")
            return
        out=["Top Vigenere guesses:"]
        for key,klen,aic in guesses:
            try: preview = vigenere_decrypt(enc,key)[:400].replace('\n',' ')
            except Exception: preview = "[error]"
            out.append(f"- key='{key}' (len={klen}) preview: {preview}")
        self._update_text(self.smart_output, "\n".join(out))

    # Tests
    def run_tests(self):
        self.stop_event.clear()
        t = threading.Thread(target=self._tests_worker); t.daemon=True; t.start()

    def _tests_worker(self):
        random.seed(1337)
        self._set_text(self.tests_output, "Starting tests...\n")
        ok=0; total=0; lines=[]
        base_msgs=["Attack at dawn!","Hide the gold!","Hello, World!","The quick brown fox jumps over 13 lazy dogs.","Numbers 012345 and punctuation, okay?","MixedCASE Words with Spaces","CrYpTo is FUN :)", "Sphinx of black quartz, judge my vow.","Pack my box with five dozen liquor jugs.","Meet @ 10:45? Bring ID #42."]
        def rand_msg():
            alphabet = string.ascii_letters + string.digits + " .,!?:;'\"-_/()[]{}@#&"
            L = random.randint(8,72)
            return ''.join(random.choice(alphabet) for _ in range(L))
        extra=[rand_msg() for _ in range(50)]
        messages = base_msgs + extra

        def check(name, plaintext, enc_fn, dec_fn):
            nonlocal ok,total
            if self.stop_event.is_set(): raise KeyboardInterrupt
            total+=1
            try:
                ct = enc_fn(plaintext)
                pt = dec_fn(ct)
                if pt == plaintext:
                    ok+=1; lines.append(f"[PASS] {name}")
                else:
                    lines.append(f"[FAIL] {name}\n  expected: {repr(plaintext)}\n  got     : {repr(pt)}")
            except Exception as e:
                lines.append(f"[ERR] {name}: {e}")

        try:
            lines.append("== Caesar ==")
            for i,msg in enumerate(messages[:30]):
                if self.stop_event.is_set(): break
                s = (i*5) % 26
                check(f"Caesar s={s} #{i}", msg, lambda x, ss=s: caesar_cipher(x, ss), lambda c, ss=s: caesar_decrypt(c, ss))
            lines.append("\n== Rot/Atbash/Reverse ==")
            check("ROT13","Hello, World!", rot13, rot13)
            check("ROT47","The quick brown fox jumps over 13 lazy dogs.", rot47, rot47)
            check("Atbash","MixedCase123!", atbash_cipher, atbash_cipher)
            check("Reverse","abcd1234", reverse_cipher, reverse_cipher)
            lines.append("\n== Encodings ==")
            for i,msg in enumerate(messages[:30]):
                if self.stop_event.is_set(): break
                check(f"Base64 #{i}", msg, lambda s: base64.b64encode(s.encode()).decode(), base64_decrypt)
                check(f"Base32 #{i}", msg, base32_encode, base32_decode)
                check(f"Ascii85 #{i}", msg, a85_encode, a85_decode)
                check(f"URL #{i}", msg, url_encode, url_decode)
                bstr = ' '.join(format(ord(ch),'08b') for ch in msg)
                total+=1
                try:
                    pt = binary_decrypt(bstr)
                    if pt==msg: ok+=1; lines.append(f"[PASS] Binary #{i}")
                    else: lines.append(f"[FAIL] Binary #{i}\n expected:{repr(msg)}\n got:{repr(pt)}")
                except Exception as e:
                    lines.append(f"[ERR] Binary #{i}: {e}")
            lines.append("\n== Vigenere/Autokey/Porta/Beaufort ==")
            keys = ["lemon","shadow","knight","alpha","delta"]
            for i,msg in enumerate(messages[:40]):
                if self.stop_event.is_set(): break
                key = keys[i%len(keys)]
                check(f"Vigenere {key} #{i}", msg, lambda x,k=key: vigenere_encrypt(x,k), lambda c,k=key: vigenere_decrypt(c,k))
                check(f"Autokey {key} #{i}", msg, lambda x,k=key: autokey_encrypt(x,k), lambda c,k=key: autokey_decrypt(c,k))
                up = msg.upper()
                check(f"Porta {key} #{i}", up, lambda x,k=key: porta(x,k), lambda c,k=key: porta(c,k))
                alpha_only = ''.join(ch for ch in msg if ch.isalpha()).upper() or "ATTACK"
                check(f"Beaufort {key} #{i}", alpha_only, lambda x,k=key: beaufort(x,k), lambda c,k=key: beaufort(c,k))
            lines.append("\n== Playfair preserve ==")
            pf_keys=["keyword","monarchy","knight","silver"]
            for i,msg in enumerate(messages[:40]):
                if self.stop_event.is_set(): break
                k = pf_keys[i%len(pf_keys)]
                check(f"Playfair preserve {k} #{i}", msg, lambda s,k=k: playfair_encrypt_preserve(s,k), lambda c,k=k: playfair_decrypt_preserve(c,k))
            lines.append("\n== Affine/Rail/XOR/Columnar ==")
            affine_params=[(5,8),(11,3),(7,2)]
            for i,msg in enumerate(messages[:40]):
                if self.stop_event.is_set(): break
                a,b = affine_params[i%len(affine_params)]
                plain = ''.join(ch for ch in msg if ch.isalpha()).upper() or "AFFINECIPHER"
                check(f"Affine a={a},b={b} #{i}", plain, lambda x,aa=a,bb=b: affine_encrypt(x,aa,bb), lambda c,aa=a,bb=b: affine_decrypt(c,aa,bb))
            xor_keys=["key","secret","delta"]
            for i,msg in enumerate(messages[:40]):
                if self.stop_event.is_set(): break
                k = xor_keys[i%len(xor_keys)]
                check(f"XOR key={k} #{i}", msg, lambda x,kk=k: xor_encrypt_to_hex(x,kk), lambda c,kk=k: xor_decrypt_from_hex(c,kk))
            # columnar encryption tests (roundtrip)
            for i,msg in enumerate(messages[:20]):
                if self.stop_event.is_set(): break
                key="ZEBRAS"
                check(f"Columnar {key} #{i}", msg, lambda x,k=key: columnar_encrypt(x,k), lambda c,k=key: columnar_decrypt(c,k))
            lines.append("\n== Morse/Baconian ==")
            check("Morse","sos help", morse_encode, morse_decode)
            check("Baconian","HELLO WORLD", bacon_encode, bacon_decode)
        except KeyboardInterrupt:
            lines.append("\n[Stopped by user]")
        lines.append(f"\nSummary: Passed {ok} / {total}")
        self._set_text(self.tests_output, "\n".join(lines))

    # helpers for text widgets
    def _update_text(self, widget, value):
        def upd():
            widget.config(state='normal'); widget.delete("1.0", tk.END); widget.insert(tk.END, value); widget.config(state='disabled')
        widget.after(0, upd)

    def _set_text(self, widget, value):
        widget.config(state='normal'); widget.delete("1.0", tk.END); widget.insert(tk.END, value); widget.config(state='disabled')

    def _append_text(self, widget, value):
        widget.config(state='normal'); widget.insert(tk.END, value); widget.config(state='disabled')

    def _load_into(self, text_widget):
        path = filedialog.askopenfilename(title="Open text file", filetypes=[("Text files","*.txt"),("All files","*.*")])
        if path:
            try:
                with open(path, 'r', encoding='utf-8', errors='replace') as f:
                    data = f.read()
                text_widget.delete("1.0", tk.END); text_widget.insert(tk.END, data)
            except Exception as e:
                messagebox.showerror("Error", f"Couldn't load file: {e}")

    def _stop(self):
        self.stop_event.set()

    def apply_settings(self):
        global REPEAT_XOR_MAX
        try:
            self.use_process_pool = bool(self.proc_var.get())
            self.dark_mode = bool(self.dark_var.get())
            self.max_workers = max(1, int(self.workers_spin.get()))
            REPEAT_XOR_MAX = max(1, int(self.repeat_spin.get()))
            self._apply_theme()
            messagebox.showinfo("Settings", f"Applied: use_process={self.use_process_pool}, workers={self.max_workers}, repeat_xor_max={REPEAT_XOR_MAX}, dark_mode={self.dark_mode}, heavy={self.heavy_mode.get()}")
        except Exception as e:
            messagebox.showerror("Settings", f"Invalid settings: {e}")

    def _set_progress_fraction(self, bar, frac):
        bar['mode'] = 'determinate'
        bar['value'] = max(0, min(100, int(frac * 100)))

    def _apply_theme(self):
        if self.dark_mode:
            bg = '#1e1e1e'; fg = '#eaeaea'; txt_bg = '#222222'
            entry_bg = '#2b2b2b'; entry_fg = '#eaeaea'
        else:
            bg = None; fg = None; txt_bg = 'white'; entry_bg='white'; entry_fg='black'
        try:
            if bg: self.root.configure(bg=bg)
            else: self.root.configure(bg=None)
        except Exception: pass
        for t in self._text_widgets:
            try:
                t.config(bg=txt_bg, fg=entry_fg, insertbackground=entry_fg)
            except Exception: pass
        for e in (getattr(self,'encrypt_key',None), getattr(self,'decrypt_key',None), getattr(self,'encrypt_shift',None), getattr(self,'decrypt_shift',None), getattr(self,'keyword_entry',None)):
            try:
                if e: e.config(bg=entry_bg, fg=entry_fg, insertbackground=entry_fg)
            except Exception: pass

# -----------------------
# Run
# -----------------------
def main():
    root = tk.Tk()
    app = EncryptorApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()
