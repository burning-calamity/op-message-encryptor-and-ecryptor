#Requires AutoHotkey v2.0
#Warn VarUnset, Off
#SingleInstance Force
#UseHook True

; Live Cipher GUI — v43 category search tags + collapsed presets + loading self-check
; Ctrl+Alt+E = Toggle encryption
; Ctrl+Alt+R = Reset cipher state
; Ctrl+Alt+Q = Quit

; ------------------------------------------------------------
; Globals
; ------------------------------------------------------------

global ALPHABET := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

global MODE_LIST := [
    "A1Z26 Greek numerals",
    "A1Z26 mod 11",
    "A1Z26 mod 9",
    "A1Z26 numbers",
    "A1Z26 resistor colors",
    "A1Z26 Roman lowercase",
    "ABC 5th edition telegraph code",
    "ABC code word variant",
    "ABC telegraph code",
    "ABC telegraph code phrase v2",
    "Acme commodity code token",
    "Acme commodity phrase code v2",
    "ACP-124 radiotelegraph code",
    "ACP-125 military message token",
    "ACP-125 operating signal v2",
    "ACP-125 radiotelephone code v2",
    "ACP-127 message format token",
    "ACP-131 operating signal token",
    "ACP-131 operating signal v2",
    "ACP-131 operating signal v3",
    "ACP-131 signal code v4",
    "Acrostic cover words",
    "ADFGVX",
    "ADFGX",
    "Adler32 token",
    "Aeneas disk cipher",
    "Aeneas fire-signal alphabet",
    "Aeneas siege disk variant",
    "Aeneas tactical disk variant",
    "Affine",
    "AIS six-bit token",
    "Albam Hebrew reciprocal v2",
    "Alberti disk",
    "Allied call sign token",
    "Alphabet consonant-first",
    "Alphabet frequency order",
    "Alphabet odd-even split",
    "Alphabet rail split",
    "Alphabet vowel-first",
    "Alternating Caesar",
    "American Morse railroad sounder v3",
    "American Morse railroad v2",
    "American Morse spaced token",
    "AMSCO block",
    "Ancient Indian Kutalipi token",
    "Anglo-Saxon runes",
    "APCO phonetic words",
    "APCO Project 14 radio code",
    "Arabic abjad",
    "Aristocrat K1 simple substitution",
    "Aristocrat K2 simple substitution",
    "Aristocrat K3 simple substitution",
    "Aristocrat K4 simple substitution",
    "Aristocrat simple substitution",
    "Aristocrat substitution classic",
    "Arithmetic toy interval",
    "Armenian actual letters",
    "Army map grid code token",
    "Arthashastra cipher wheel style",
    "ASCII base12 byte",
    "ASCII base13 byte",
    "ASCII base14 byte",
    "ASCII base15 byte",
    "ASCII base17 byte",
    "ASCII base18 byte",
    "ASCII base19 byte",
    "ASCII base21 byte",
    "ASCII base22 byte",
    "ASCII base23 byte",
    "ASCII base25 byte",
    "ASCII base27 byte",
    "ASCII base28 byte",
    "ASCII base29 byte",
    "ASCII base3 byte",
    "ASCII base31 byte",
    "ASCII base33 byte",
    "ASCII base34 byte",
    "ASCII base35 byte",
    "ASCII base36 byte",
    "ASCII base37 byte",
    "ASCII base38 byte",
    "ASCII base39 byte",
    "ASCII base4 byte",
    "ASCII base40 byte",
    "ASCII base41 byte",
    "ASCII base42 byte",
    "ASCII base43 byte",
    "ASCII base44 byte",
    "ASCII base5 byte",
    "ASCII base52 byte",
    "ASCII base6 byte",
    "ASCII binary 8-bit",
    "ASCII decimal",
    "ASCII decimal padded",
    "ASCII hex lowercase",
    "Assembly DB hex",
    "Atbah Hebrew substitution v2",
    "Atbash",
    "Aurebesh tokens",
    "Austro-Hungarian cipher disk",
    "Autoclave cipher historical v2",
    "Autokey Beaufort",
    "Autokey field cipher",
    "Autokey keyed alphabet",
    "Autokey primer field cipher",
    "Autokey reversed alphabet",
    "Autokey Vigenere",
    "Avestan letters",
    "AX25 callsign token",
    "AZERTY to QWERTY",
    "Aztec barcode token",
    "Aztec binary token",
    "Aztec compact word token",
    "Babington plot cipher token",
    "Babington plot nomenclator v2",
    "Backslang reverse",
    "Bacon biliteral custom",
    "Bacon biliteral Francis Bacon 1623",
    "Bacon biliteral modern 26-letter",
    "Bacon biliteral original 24-letter",
    "Bacon italic-roman stego token",
    "Bacon twenty-four-letter alphabet",
    "Baconian 0-1 compact",
    "Baconian 12345",
    "Baconian 24 I/J",
    "Baconian 24-letter classic",
    "Baconian 26-letter modern",
    "Baconian A/B",
    "Baconian Baudot",
    "Baconian biliteral classic",
    "Baconian binary",
    "Baconian binary spaced",
    "Baconian braille",
    "Baconian chess pieces",
    "Baconian dice faces",
    "Baconian dots dashes",
    "Baconian emoji",
    "Baconian five-bit binary",
    "Baconian flag token",
    "Baconian Greek",
    "Baconian hexadecimal",
    "Baconian high-low",
    "Baconian lowercase uppercase",
    "Baconian morse",
    "Baconian quaternary tag",
    "Baconian quinary digits",
    "Baconian reversed",
    "Baconian Roman",
    "Baconian roman binary",
    "Baconian slash",
    "Baconian visible whitespace",
    "Balanced quinary index",
    "Balanced senary index",
    "Balanced ternary index",
    "Base100 emoji byte",
    "Base11 index",
    "Base12 index",
    "Base16 index",
    "Base16 separated per letter",
    "Base20 index",
    "Base24 index",
    "Base26 A0Z25",
    "Base3 per letter",
    "Base30 index",
    "Base32 no padding per letter",
    "Base32 per letter",
    "Base32Hex per letter",
    "Base36 per letter",
    "Base4 per letter",
    "Base45 byte token",
    "Base45 per letter",
    "Base5 index",
    "Base58 byte token",
    "Base58 index",
    "Base6 index",
    "Base62 index",
    "Base64 index",
    "Base64 no padding per letter",
    "Base64 per letter",
    "Base64URL per letter",
    "Base7 index",
    "Base8 per letter",
    "Base85 ascii85 framed",
    "Base85 index",
    "Base85 per letter",
    "Base9 per letter",
    "Base91 byte token",
    "Base91 index token",
    "Base91 per letter",
    "Base92 per letter",
    "Bash hex token",
    "BATCO authentication table v4",
    "BATCO map coordinate style",
    "BATCO phrase table v2",
    "BATCO tactical code",
    "BATCO tactical code grid v3",
    "BATCO tactical grid v2",
    "BATCO tactical phrase v3",
    "BATCO tactical table v5",
    "Baudot ITA1 code v3",
    "Baudot ITA1 telegraph v2",
    "Baudot ITA2",
    "Baudot ITA2 figure shift v3",
    "Baudot ITA2 figures-letters field",
    "Baudot ITA2 teleprinter v2",
    "Baudot ITA2 teleprinter v4",
    "Baudot Murray token compact",
    "Baudot reversed bits",
    "Baudot tape holes",
    "Bazeries 1891 cylinder variant",
    "Bazeries block",
    "Bazeries cipher classic",
    "Bazeries cylinder style",
    "Bazeries number-key classic v2",
    "Bazeries type 2 classic",
    "BCD 2421 token",
    "BCD 5211 token",
    "BCD A1Z26",
    "BCH toy syndrome",
    "Beale book cipher Declaration v3",
    "Beale book number token v2",
    "Beale cipher book style",
    "Beale cipher Declaration book v2",
    "Beale cipher pamphlet v4",
    "Beale cipher paper one",
    "Beale cipher paper three",
    "Beale cipher paper two",
    "Beale Declaration book cipher v5",
    "Beale variant book cipher",
    "Beaufort",
    "Bech32 index",
    "Bell number token",
    "Bellaso",
    "Bencode string token",
    "Bengali letters",
    "Bentley code word variant",
    "Bentley complete phrase code token",
    "Bentley complete phrase code v2",
    "Bentley second phrase code token",
    "Bentleys phrase code",
    "Bible book cipher chapter verse",
    "Bible code book cipher v3",
    "Bifid full period",
    "Bifid pairs",
    "Binary 5-bit",
    "Binary 6-bit index",
    "Binary ASCII 7-bit",
    "Binary endian word",
    "Bit reverse byte",
    "Black Chamber code token",
    "Blum Blum Shub toy",
    "Bold fraktur letters",
    "Bold script letters",
    "Book cipher Bible KJV v2",
    "Book cipher chapter-verse token",
    "Book cipher classic",
    "Book cipher dictionary page word",
    "Book cipher index",
    "Book cipher page line word v3",
    "Book cipher page-line-letter v2",
    "Boustrophedon route block",
    "Boustrophedon route classic",
    "Box drawing code",
    "Braille",
    "Braille dots token",
    "Braille grade 1",
    "BREVITY airborne codeword token",
    "Brevity code ACP token",
    "Brevity code aviation ACP",
    "Brevity codeword token",
    "British Government Code Cypher v2",
    "British Government Code token",
    "British Naval Cypher No 3 token",
    "British Naval Cypher No 3 v2",
    "British trench code 1918 v2",
    "British trench codebook token",
    "British Typex 5-rotor style",
    "Brotli meta token",
    "BWT rotation token",
    "Byte pair hex token",
    "C string escape",
    "Cable code 5-figure",
    "Cadenus block",
    "Caesar",
    "Caesar box mini block",
    "Caesar custom alphabet",
    "Calculator spelling",
    "Canadian syllabics",
    "Cantor pairing token",
    "Catalan number token",
    "Celestial alphabet Agrippa v2",
    "Celestial alphabet tokens",
    "ChaCha toy token",
    "Chaocipher",
    "Chaocipher alphabet classic v2",
    "Chaocipher Byrne classic",
    "Chappe optical telegraph French v2",
    "Chappe optical telegraph v2",
    "Chappe optical telegraph v4",
    "Chappe semaphore arm positions v3",
    "Chappe semaphore numbered",
    "Chappe semaphore token",
    "Checkerboard 10x10 token",
    "Checkerboard ACA cipher",
    "Checkerboard fractionating classic",
    "Checkerboard Morse rows",
    "Checkerboard serial",
    "Checkerboard transposition ACA v2",
    "Checkerboard transposition period 25",
    "Cherokee letters",
    "Chess coordinates",
    "Chessboard coordinates",
    "Chinese remainder token",
    "Choctaw code talker token",
    "Circled letters",
    "Cirth runes",
    "Cistercian monk numeral cipher",
    "Cistercian numeral letter code",
    "Cistercian numerals",
    "Clave",
    "Codabar alphabet token",
    "Codabar token",
    "Code11 check token",
    "Code128 token",
    "Code39 full ASCII token",
    "Code39 token",
    "Code93 token",
    "Codebook diplomatic",
    "Colemak keyboard",
    "Colemak to QWERTY",
    "Columnar transposition block",
    "Commercial cable code ABC v2",
    "Commercial cable code pronounceable v2",
    "Commercial Cable Code token",
    "Commercial cable pronounceable code",
    "Commercial code 5-letter groups v2",
    "Commercial code 5-number groups v2",
    "Commercial code Bentley second phrase",
    "Commercial code Lieber code",
    "Commercial code word",
    "Commercial codebook 5-letter",
    "Commercial codebook four-letter",
    "Condi",
    "Confederate cipher disk",
    "Confederate cipher wheel v2",
    "Confederate cipher wheel v3",
    "Confederate route transposition",
    "Confederate signal disk 1860s",
    "Consonant Caesar",
    "Coordinate 0-based",
    "Copiale cipher glyph cluster v5",
    "Copiale cipher glyph v2",
    "Copiale cipher token",
    "Copiale code glyph token v3",
    "Copiale glyph cluster style v3",
    "Copiale homophonic codebook",
    "Copiale homophonic token v2",
    "Copiale manuscript glyph v4",
    "Copiale substitution style",
    "Coptic letters",
    "Cornelius Agrippa Theban cipher",
    "CRC12 token",
    "CRC16 CCITT token",
    "CRC16 token",
    "CRC24 toy token",
    "CRC32 token",
    "CRC4 token",
    "CRC5 USB token",
    "CRC6 token",
    "CRC64 token",
    "CRC7 token",
    "CRC8 token",
    "Crockford Base32 index",
    "Crockford byte token",
    "CSharp unicode escape",
    "CSS escape short",
    "CSS hex escape",
    "CSS unicode padded",
    "CSV hex cell token",
    "CSV quoted token",
    "Cube Caesar shift",
    "Cubed A1Z26",
    "Cypriot syllabary tokens",
    "Cyrillic actual letters",
    "Cyrillic lookalike",
    "Damm check token",
    "Dancing Men tokens",
    "Data URI token",
    "DataMatrix ASCII token",
    "DataMatrix C40 token",
    "DataMatrix codeword token",
    "Decimal A0Z25",
    "Decimal entity padded",
    "Declaration book cipher 1776 style",
    "Deflate block marker",
    "Devanagari letters",
    "Diana cipher",
    "Dice pair code",
    "Diceware coordinate token",
    "Dictionary code index",
    "Dictionary code page-line-word",
    "Dictionary code word number v3",
    "Digital root Caesar shift",
    "Digrafid ACA cipher",
    "Digrafid ACA period 5",
    "Digrafid cipher ACA v3",
    "Digrafid fractionated digraph v2",
    "Digrafid German field style",
    "Digrafid period 5",
    "Diplomatic five-figure code",
    "Diplomatic five-letter book code",
    "Diplomatic four-digit book code",
    "Diplomatic four-figure code",
    "DNA triplet code",
    "DNS label token",
    "Domino tile code",
    "Dorabella cipher arc token v4",
    "Dorabella cipher Elgar style",
    "Dorabella cipher symbol style",
    "Dorabella curved symbols v2",
    "Dorabella Elgar cipher v2",
    "Dorabella Elgar script v5",
    "Dorabella Elgar symbol set v3",
    "Dorabella symbol alphabet v2",
    "Double columnar block",
    "Double Playfair pairs",
    "Double-square horizontal classic",
    "Double-square vertical classic",
    "DRYAD KTC 1400 style",
    "DRYAD numeral authentication v3",
    "DRYAD numeral authentication v5",
    "DRYAD numeral cipher",
    "DRYAD tactical authentication v2",
    "DRYAD tactical numeral sheet v4",
    "DRYAD tactical numeral v3",
    "DRYAD two-digit table v2",
    "Dvorak to QWERTY",
    "EAN letter checksum",
    "EAN-13 check token",
    "EAN-8 check token",
    "EBCDIC decimal",
    "EBCDIC hex",
    "Egyptian alphabet tokens",
    "Elder Futhark rune cipher v2",
    "Elder Futhark runes",
    "Elias delta token",
    "Elias gamma token",
    "Elias omega token",
    "Elizabeth I court cipher v2",
    "Elizabethan secretary cipher v2",
    "Emoji alphabet",
    "Enigma Abwehr G style v2",
    "Enigma Abwehr G312 style",
    "Enigma commercial D live",
    "Enigma commercial D v4",
    "Enigma D commercial export v2",
    "Enigma D commercial key live",
    "Enigma D commercial style live",
    "Enigma G Abwehr key v3",
    "Enigma G Abwehr live",
    "Enigma G Abwehr v4",
    "Enigma K Swiss army v4",
    "Enigma K Swiss key live",
    "Enigma K Swiss railway v2",
    "Enigma Kenngruppenbuch token",
    "Enigma Kurzsignalheft token",
    "Enigma M3",
    "Enigma M4",
    "Enigma Railway live",
    "Enigma Railway Rocket v3",
    "Enigma Swiss K live",
    "Enigma T Tirpitz key live",
    "Enigma T Tirpitz naval v2",
    "Enigma Tirpitz Japan v4",
    "Enigma Tirpitz live",
    "Enigma Uhr box style",
    "Enigma Uhr plugboard live",
    "Enigma Uhr plugboard v3",
    "Enigma Uhr switch board v2",
    "Enigma Uhr switch style",
    "Enigma weather short signal v2",
    "Enigma Zahlwerk live",
    "Enochian alphabet Dee token v2",
    "Enochian alphabet tokens",
    "Etruscan tokens",
    "Excess-3 BCD token",
    "Facing identification mark",
    "Factoradic index",
    "Factorial index",
    "Federal cipher disk Civil War",
    "Fialka Cyrillic wheel style",
    "Fialka Latin training v5",
    "Fialka Latin wheel style",
    "Fialka M-125 30-wheel v3",
    "Fialka M-125 Cyrillic live v2",
    "Fialka M-125 Cyrillic v5",
    "Fialka M-125 Latin live v2",
    "Fialka M-125 Latin training v3",
    "Fialka M-125 live",
    "Fialka M-125 wheel style",
    "Fialka M-125-3 live",
    "Fibonacci Caesar shift",
    "Fibonacci LFSR toy",
    "Fibonacci numbers",
    "Fibonacci universal token",
    "Fibonacci word token",
    "Field cipher disk M-138 style",
    "Fish machine teleprinter token",
    "Five-figure code group diplomatic",
    "Five-letter code group diplomatic",
    "Flag token alphabet",
    "Fleissner grille block",
    "Fletcher16 token",
    "Fletcher32 token",
    "Four-square 6x6 pairs",
    "Four-square pairs",
    "Fractionated Morse",
    "Fractionated Morse ACA classic",
    "Fractionated Morse ACA field variant",
    "Fractionated Morse ACA v2",
    "Fractionated Morse ACA v3",
    "Fractionated Morse base3",
    "Fractionated Morse classic",
    "Fractionated Morse numeric",
    "Fractionated tap code",
    "Fraktur letters",
    "Freemason pigpen dot variant",
    "Freemason pigpen dotted",
    "Freemason pigpen grid v3",
    "Freemason pigpen X-grid",
    "French Army cipher disk 1914",
    "French diplomatic nomenclator 1700",
    "French trench code 1916 v2",
    "French trench codebook token",
    "Frequency keyed substitution",
    "Fullwidth letters",
    "GEDEFU 36 field checkerboard",
    "GEDEFU 36-coordinate cipher",
    "GEDEFU checkerboard 6x6 v2",
    "GEDEFU field cipher v4",
    "GEDEFU German checkerboard v3",
    "GEDEFU German field cipher v2",
    "Gematria number cipher token",
    "Geometric shape alphabet",
    "Georgian actual letters",
    "German trench code 1917 v2",
    "German trench codebook token",
    "Glagolitic letters",
    "Go rune token",
    "Godel prime token",
    "Gold-Bug cipher symbols",
    "Gold-Bug Poe cipher v5",
    "Gold-Bug Poe exact-symbol style",
    "Gold-Bug Poe substitution v4",
    "Gold-Bug Poe symbol token v4",
    "Gold-Bug Poe symbols v2",
    "Gold-Bug substitution Poe v3",
    "Golomb Rice token",
    "Gothic letters",
    "Grandpre ACA cipher",
    "Grandpre checkerboard ACA v2",
    "Grandpre cipher classic",
    "Grandpre coordinate",
    "Gray code 5-bit",
    "Gray code 8-bit",
    "Gray code reflected",
    "Great Cipher homophone v3",
    "Great Cipher nulls and syllables",
    "Great Cipher syllable-number v2",
    "Greek acrophonic token",
    "Greek actual letters",
    "Greek alphabet names",
    "Greek isopsephy",
    "Greek lookalike",
    "Greek Skytale military dispatch",
    "Green cipher machine live",
    "Grid reference military MGRS token",
    "Grille mask block",
    "Gromark",
    "Gromark ACA classic",
    "Gromark ACA primer transposition v3",
    "Gromark keyed primer variant",
    "Gromark mixed alphabet v4",
    "Gromark primer chain v4",
    "Gromark primer transposition ACA v2",
    "Gromark running digits",
    "Gromark running key ACA",
    "Gronsfeld",
    "Gronsfeld progressive",
    "GS1 AI token",
    "GUID byte token",
    "Habsburg diplomatic nomenclator v2",
    "Hagelin B-21 pinwheel style",
    "Hagelin BC-38 style live",
    "Hagelin BC-38 Swedish field",
    "Hagelin BC-52 live",
    "Hagelin C-35 lug style",
    "Hagelin C-35 pinwheel v2",
    "Hagelin C-36 pin-lug style",
    "Hagelin C-36 pinwheel v3",
    "Hagelin C-36 style live",
    "Hagelin C-36 Swedish style v2",
    "Hagelin C-38 converter style",
    "Hagelin C-38 converter v3",
    "Hagelin C-38 live",
    "Hagelin C-38 style live",
    "Hagelin C-446 pocket style",
    "Hagelin C-446 pocket v2",
    "Hagelin C-446 style",
    "Hagelin C-52 live",
    "Hagelin C-52 lug cage v3",
    "Hagelin C-52 lug cage v5",
    "Hagelin C-52 pinwheel v2",
    "Hagelin C-series toy stream",
    "Hagelin CD-57 live",
    "Hagelin CD-57 pocket style v2",
    "Hagelin CD-57 pocket v3",
    "Hagelin CD-57 pocket v5",
    "Hagelin CX-52 advanced v3",
    "Hagelin CX-52 irregular motion v4",
    "Hagelin CX-52 irregular style",
    "Hagelin CX-52 live",
    "Hagelin CX-52 pinwheel v2",
    "Hagelin CX-52 style live",
    "Hagelin CX-52 v5",
    "Hamming 15,11 token",
    "Hamming 7,4 token",
    "Hamming parity syndrome",
    "Hangul jamo token",
    "Happy number token",
    "Headline puzzle ACA",
    "Headline puzzle words",
    "Hebern 1921 rotor",
    "Hebern 5-rotor navy live",
    "Hebern electric code machine v3",
    "Hebern electric rotor",
    "Hebern electric rotor five-wheel",
    "Hebern five-rotor machine v4",
    "Hebern five-rotor style live",
    "Hebern one-rotor simulator",
    "Hebern rotor five-wheel v3",
    "Hebern rotor machine",
    "Hebern single rotor 1920s v2",
    "Hebern single rotor v4",
    "Hebrew actual letters",
    "Hebrew Albam substitution",
    "Hebrew Atbah substitution",
    "Hebrew gematria",
    "Heliograph field Morse v2",
    "Heliograph Morse field code",
    "Hellschreiber token",
    "Hex ASCII",
    "Hex color code",
    "Hex entity padded",
    "Hexdump byte",
    "Hill 2x2 coordinate token",
    "Hill 2x2 pairs",
    "Hill 3x3 block",
    "Hill 3x3 coordinate token",
    "Hill cipher 2x2 classic",
    "Hill cipher 3x3 classic",
    "Hill coordinate token",
    "Hill mod26 vector token",
    "Hiragana phonetic",
    "Hollerith punch code",
    "Homophonic court cipher v2",
    "Homophonic French 1700s v2",
    "Homophonic French court cipher",
    "Homophonic frequency table 1700s",
    "Homophonic nomenclator 1400s",
    "Homophonic numbers",
    "Homophonic Papal cipher 1600s",
    "Homophonic Spanish 1600s v2",
    "Homophonic Spanish court cipher",
    "Homophonic substitution",
    "Homophonic substitution classic",
    "Homophonic syllabary 1600s",
    "Homophonic Zodiac style table v6",
    "Homophonic Zodiac table v7",
    "HTML entity",
    "HTML entity hex padded",
    "HTML hex entity",
    "HTML named alpha token",
    "HTML named fallback",
    "Huffman fixed token",
    "Huffman toy token",
    "HY-2 voice scrambler style v2",
    "HY-2 voice scrambler token",
    "IBM card row punch",
    "ICS flag hoist two-letter",
    "INI hex token",
    "Intel asm char",
    "Intel HEX record",
    "Interleaved 2 of 5 pair",
    "International Code of Signals 1931",
    "International Code of Signals 1965",
    "International Code of Signals 1969 v2",
    "International Code of Signals flag token",
    "International Code of Signals flag v3",
    "International Code Signals single flag",
    "International Code Signals two flag",
    "International maritime flag hoist v2",
    "International Morse 1865",
    "International Morse spaced token",
    "International signal phrases",
    "Interrupted key ACA v2",
    "Interrupted key cipher ACA v3",
    "Invisible unicode visible",
    "IPv4 octet token",
    "IPv6 hextet token",
    "ISBN letter checksum",
    "ISBN-10 check token",
    "ISBN-13 check token",
    "ITA2 letters only token",
    "ITF token",
    "Japanese army codebook token",
    "Japanese Coral cipher machine style",
    "Japanese Coral machine v2",
    "Japanese Jade machine style token",
    "Japanese Jade machine v2",
    "Japanese naval code JN-25 token",
    "Japanese Orange attaché machine v2",
    "Japanese Orange attaché v3",
    "Japanese Red attaché machine v3",
    "Japanese Red machine v2",
    "Japanese Red machine v4",
    "Java unicode escape",
    "JavaScript hex escape",
    "Jefferson disk",
    "JN-25 naval codebook v2",
    "JN-40 merchant code token",
    "Johnson code token",
    "JSON string escape",
    "Kabbalistic notarikon token",
    "Kaktovik numeral token",
    "Kamasutra paired alphabet classic",
    "Kamasutra substitution",
    "Katakana phonetic",
    "Kautiliya secret writing style",
    "Keyboard adjacent left",
    "Keyboard adjacent right",
    "Keyboard Caesar",
    "Keyboard column code",
    "Keyboard coordinates",
    "Keyboard diagonal code",
    "Keyboard mirror",
    "Keyed ADFGVX",
    "Keyed ADFGX",
    "Keyed alphabet Caesar",
    "Keyed alphabet Fibonacci",
    "Keyed alphabet prime",
    "Keyed alphabet reciprocal",
    "Keyed alphabet triangular",
    "Keyed Atbash",
    "Keyed Caesar",
    "Keyed Polybius square",
    "Keyed progressive Caesar",
    "Keyed reciprocal substitution",
    "Keyed reverse substitution",
    "Keyed Tap coordinate",
    "Keyword alphabet K1 ACA",
    "Keyword alphabet K2 ACA",
    "Keyword alphabet K3 ACA",
    "Keyword alphabet K4 ACA",
    "Keyword mixed alphabet classic",
    "Keyword substitution",
    "Keyword transposed alphabet",
    "KIX 4-state token",
    "KL-51 field cipher token",
    "KL-7 ADONIS daily key v4",
    "KL-7 ADONIS live",
    "KL-7 ADONIS military key v3",
    "KL-7 ADONIS rotor live v2",
    "KL-7 ADONIS rotor style",
    "KL-7 ADONIS rotor v5",
    "KL-7 ADONIS style",
    "KL-7 rotor cipher live",
    "KL-7 training key style",
    "Knights Templar cipher classic",
    "Knock binary token",
    "Knock code",
    "Knuth checksum token",
    "Kryha cipher machine",
    "Kryha electric style live",
    "Kryha Liliput disk v2",
    "Kryha Liliput machine",
    "Kryha Liliput pocket cipher",
    "Kryha Liliput pocket style",
    "Kryha machine daily key v3",
    "Kryha machine stepping v2",
    "Kryha Standard cipher machine v4",
    "Kryha Standard disk 1924 v3",
    "Kryha Standard machine style",
    "Kryha Standard pocket machine v2",
    "KW-26 online rotor stream v4",
    "KW-26 ROMULUS line cipher v5",
    "KW-26 ROMULUS stream style",
    "KW-26 ROMULUS stream v2",
    "KW-26 ROMULUS teleprinter v3",
    "KW-37 fleet broadcast cipher token",
    "KW-7 ORESTES line cipher v4",
    "KW-7 ORESTES line cipher v5",
    "KW-7 ORESTES stream style",
    "KW-7 ORESTES stream v2",
    "KW-7 ORESTES teleprinter v3",
    "LAPD phonetic words",
    "LaTeX mathbb command",
    "LaTeX mathcal command",
    "Latin alphabet names",
    "Latin reverse custom",
    "LCG checksum token",
    "LCG stream hex",
    "LDAP hex escape",
    "LEB128 token",
    "Leet basic",
    "Lehmer code token",
    "Letter frequency rank",
    "Letter index hex",
    "Lieber code diplomatic token",
    "Lieber field code 1915 token",
    "Lieber field code token v2",
    "Linear B tokens",
    "Lorenz SZ40 chi wheel live",
    "Lorenz SZ40 chi wheel v3",
    "Lorenz SZ40 chi wheels v2",
    "Lorenz SZ40 chi wheels v5",
    "Lorenz SZ40 live",
    "Lorenz SZ40 toy stream",
    "Lorenz SZ40/42 chi stream v4",
    "Lorenz SZ42 chi psi style",
    "Lorenz SZ42 live",
    "Lorenz SZ42 motor wheel v2",
    "Lorenz SZ42 motor wheels v3",
    "Lorenz SZ42 psi motor v3",
    "Lorenz SZ42 psi mu stream v5",
    "Lorenz SZ42 psi wheel live",
    "Lorenz SZ42 psi wheel v4",
    "Lorenz SZ42 psi wheels v6",
    "Lorenz SZ42 teleprinter v2",
    "Lorenz SZ42A live",
    "Lorenz SZ42B live",
    "Lorenz SZ42c style",
    "Louis XIV diplomatic syllables v4",
    "Louis XIV Great Cipher numbers v6",
    "Louis XIV Great Cipher style",
    "Louis XIV nomenclator v2",
    "Louis XIV syllabary table v5",
    "Louis XIV syllable cipher v3",
    "LRC token",
    "Lucas Caesar shift",
    "Luhn check token",
    "LZW dictionary token",
    "M-138-A strip cipher",
    "M-138-A strip cipher v2",
    "M-209 Hagelin style",
    "M-94 cylinder style",
    "Malachim alphabet Agrippa v2",
    "Malachim alphabet tokens",
    "Malachim occult alphabet v2",
    "Map coordinate artillery code",
    "Maritime signal code 1931",
    "Maritime signal flags",
    "Marryat naval signal book v3",
    "Marryat signal code token",
    "Mary Queen of Scots cipher v3",
    "Mary Stuart symbol nomenclator v2",
    "Masonic pigpen classic",
    "Masonic pigpen prison variant",
    "Masonic pigpen variant",
    "Masonic tic-tac-toe pigpen",
    "Mathematical bold italic",
    "Mathematical bold letters",
    "Mathematical double-struck",
    "Mathematical italic letters",
    "Maxicode word token",
    "Mayan bar-dot token",
    "MD5 toy token",
    "MessagePack hex token",
    "METAR abbreviation code token",
    "Mexican Army cipher disk",
    "Mexican Army cipher disk 1916 v2",
    "Mexican cipher disk 1916 variant",
    "MICR E13B token",
    "MIME quoted word B",
    "MIME quoted word Q",
    "MIPS ascii byte",
    "Mirror text alphabet",
    "Mlecchita Vikalpa substitution",
    "Modular cube index",
    "Modular inverse index",
    "Modular square index",
    "Modulo 9 index",
    "Monastic manuscript cipher token",
    "Monome-Dinome",
    "Monome-Dinome ACA classic",
    "Monome-Dinome checkerboard v2",
    "Monome-Dinome checkerboard v4",
    "Monome-dinome checkerboard WWI",
    "Monome-Dinome French army variant",
    "Monome-Dinome French trench v2",
    "Monome-Dinome trench checkerboard v3",
    "Monome-Dinome trench variant",
    "Monospace letters",
    "Moon phase alphabet",
    "Moon type tokens",
    "Morbit ACA classic",
    "Morbit ACA classic v2",
    "Morbit ACA digit pairs",
    "Morbit binary pairs",
    "Morbit Morse",
    "Morbit Morse ACA classic v2",
    "Morbit Morse pair cipher v2",
    "Morbit ternary pairs",
    "Morse American railroad v2",
    "Morse American railroad v4",
    "Morse American token",
    "Morse arrows",
    "Morse base3 token",
    "Morse binary 01",
    "Morse binary 10",
    "Morse blocks",
    "Morse bullet dash",
    "Morse compact 01",
    "Morse compact digits",
    "Morse Continental code 1848",
    "Morse Continental field code v3",
    "Morse dash count",
    "Morse decimal token",
    "Morse dot count",
    "Morse emoji",
    "Morse hex token",
    "Morse International 1865 v2",
    "Morse international radio v4",
    "Morse Japanese Wabun token",
    "Morse landline American",
    "Morse length code",
    "Morse length-dash-dot",
    "Morse letters",
    "Morse phone taps",
    "Morse prosign token",
    "Morse pulse widths",
    "Morse reverse",
    "Morse star bar",
    "Morse syllable token",
    "Morse tap digits",
    "Morse timed token",
    "Morse Unicode symbols",
    "Morse vowels consonants",
    "Morse with slash",
    "Morse word code",
    "Motorola S-record",
    "Move-to-front index",
    "Move-to-front rank token",
    "MSI check token",
    "Multiplicative progressive",
    "Murray code",
    "Murray code teleprinter field",
    "Murray code teleprinter v2",
    "Murray punched tape",
    "Murray reversed bits",
    "Murray teleprinter code v3",
    "Murray teleprinter code v4",
    "Music notes",
    "Myszkowski transposition block",
    "Nabataean tokens",
    "Napoleonic codebook 1812 token",
    "Napoleonic diplomatic codebook v2",
    "Napoleonic field cipher",
    "Napoleonic Grand Chiffre style",
    "NATO words",
    "Navajo code talker alphabet",
    "Navajo code talker token",
    "Navajo code talker word v2",
    "Naval code flag group token",
    "Naval flag hoist ICS v2",
    "Naval signal book token",
    "Negative circled letters",
    "NEMA 1947 style",
    "NEMA army training key v4",
    "NEMA Kriegsmobilmachung live",
    "NEMA Swiss 10-wheel army v3",
    "NEMA Swiss 10-wheel style",
    "NEMA Swiss army v5",
    "NEMA Swiss machine live",
    "NEMA Swiss rotor 10-wheel v2",
    "NEMA training key style",
    "Netstring token",
    "Nibble swap hex",
    "Nicodemus ACA cipher v4",
    "Nicodemus ACA classic",
    "Nicodemus ACA transposition v3",
    "Nicodemus block",
    "Nihilist numeric stream",
    "Nihilist substitution",
    "Nomenclator 1700s diplomatic",
    "Nomenclator Bourbon court",
    "Nomenclator code classic",
    "Nomenclator Elizabethan court",
    "Nomenclator Habsburg court",
    "Nomenclator Mary Queen of Scots",
    "Nomenclator Napoleonic code",
    "Nomenclator Papal cipher",
    "Nomenclator Renaissance envoy",
    "Nomenclator Spanish court 1600s",
    "Nomenclator Stuart court",
    "Nomenclator syllable 1800s",
    "Nomenclator syllable code",
    "Nomenclator Thirty Years War",
    "Nomenclator Venetian 1500s",
    "Nomenclator Venetian envoy v2",
    "NOTAM abbreviation code token",
    "Null acrostic words",
    "Null cipher acrostic classic",
    "Null cipher every third",
    "Numbers station Cyrillic style token",
    "Numbers station Czech groups",
    "Numbers station English groups v2",
    "Numbers station five-digit groups",
    "Numbers station five-figure v2",
    "Numbers station five-letter v2",
    "Numbers station German groups",
    "Numbers station one-time pad token",
    "Numbers station Russian groups v2",
    "Numbers station Spanish groups",
    "OCR-A token",
    "Octal A1Z26",
    "Octal ASCII",
    "Octal escape token",
    "Ogham cipher medieval v2",
    "Ogham cryptic scoreline cipher",
    "Ogham edge-notch cipher v2",
    "Ogham letters",
    "Ogham stemline secret marks",
    "Old Persian cuneiform",
    "Old Turkic runes",
    "One-hot index token",
    "One-time pad A-Z",
    "One-time pad decimal groups",
    "One-time pad decimal groups v3",
    "One-time pad diplomatic 5-groups",
    "One-time pad five-figure groups",
    "One-time pad five-letter groups",
    "One-time pad letter groups v2",
    "One-time pad letter groups v3",
    "One-time pad numeric classic",
    "OpenPGP armor token",
    "Optical telegraph station code",
    "Optical telegraph token",
    "Orange Japanese naval attache",
    "OTP additive number groups",
    "OTP base26 token",
    "OTP letter pad classic",
    "OTP numeric token",
    "OTP subtractive letter groups",
    "Ottoman chancery code token v2",
    "Ottoman diplomatic code token",
    "Pahlavi tokens",
    "Papal Curia nomenclator v2",
    "Papal nomenclator Vatican style",
    "Parenthesized letters",
    "Parity bit token",
    "Patristocrat K1 no-space substitution",
    "Patristocrat K2 no-space substitution",
    "Patristocrat K3 no-space substitution",
    "Patristocrat K4 no-space substitution",
    "Patristocrat no spaces",
    "Patristocrat substitution classic",
    "PDF417 codeword token",
    "PDF417 compact token",
    "PEM armor token",
    "Percent lowercase",
    "Percent uppercase spaced",
    "Perfect square marker",
    "Periodic atomic numbers",
    "Periodic element symbols",
    "Periodic Gromark ACA",
    "Periodic Gromark v2",
    "Perl hex token",
    "PGP word list token",
    "Pharmacode token",
    "Phillips cipher",
    "Phillips cipher ACA v2",
    "Phillips cipher sliding square v2",
    "Phillips ciphertext slide variant",
    "Phillips classic",
    "Phillips code naval token",
    "Phillips code press abbreviation",
    "Phillips naval code word v2",
    "Phillips plaintext slide variant",
    "Phillips press code telegraph v2",
    "Phillips RC classic",
    "Phillips RC sliding square v3",
    "Phillips RC variant ACA v2",
    "Phillips RC variant v2",
    "Phillips sliding square v4",
    "Phoenician letters",
    "Phone multitap",
    "Phone T9 digit",
    "Pig Latin",
    "Pigpen Freemason classic v2",
    "Pigpen Freemason dotted v3",
    "Pigpen grid code",
    "Pigpen Masonic dotted v3",
    "Pigpen symbols",
    "PLANET digit token",
    "Planet sequence alphabet",
    "Playfair 6x6 pairs",
    "Playfair pairs",
    "Playing card code",
    "Poem code agent variant v3",
    "Poem code SOE style",
    "Poem code transposition SOE v2",
    "Poem code transposition token",
    "Pollux ACA classic",
    "Pollux ACA digit map",
    "Pollux binary 0-1-2",
    "Pollux emoji 0-1-2",
    "Pollux fractionated Morse classic",
    "Pollux Morse",
    "Pollux Morse ACA classic v2",
    "Pollux Morse digit cipher v2",
    "Polybius square",
    "Popham flag code Trafalgar v3",
    "Popham flag telegraph naval",
    "Popham naval flag code v2",
    "Porta",
    "Postal abbreviation token",
    "POSTNET digit token",
    "PostScript char token",
    "PostScript glyph name",
    "Power residue index",
    "PowerShell char token",
    "Prime Caesar shift",
    "Prime numbers",
    "Prime product index",
    "Printable ASCII Caesar",
    "Prison tap code",
    "Progressive Caesar",
    "Progressive key ACA v2",
    "Progressive key cipher ACA v3",
    "Progressive key diplomatic",
    "Progressive Porta",
    "Progressive Vigenere",
    "Protein name code",
    "Prussian field cipher disk",
    "Punycode ascii token",
    "Purple 6-20 stepping switch v3",
    "Purple 6-20 switch live",
    "Purple 97-shiki diplomatic",
    "Purple cipher live",
    "Purple diplomatic 1939 style",
    "Purple diplomatic machine v6",
    "Purple diplomatic switchboard v4",
    "Purple Japanese diplomatic v5",
    "Purple sixes-twenties live",
    "Purple stepping switches v2",
    "Python bytes token",
    "Python unicode escape",
    "Q-code aviation maritime v4",
    "Q-code aviation token",
    "Q-code maritime aviation v2",
    "Q-code maritime token",
    "Q-code radiotelegraph v3",
    "Q-code telegraph token",
    "QNH Q-code token",
    "QR alphanumeric index",
    "QR alphanumeric value",
    "QR byte mode token",
    "QR format bits token",
    "QR numeric token",
    "Quadratic residue token",
    "Quagmire I",
    "Quagmire II",
    "Quagmire III",
    "Quagmire IV",
    "Quoted printable",
    "Quoted printable soft token",
    "QWERTY adjacent down",
    "QWERTY adjacent up",
    "QWERTY row rotate",
    "QWERTY to AZERTY",
    "QWERTY to Dvorak",
    "QWERTZ keyboard",
    "RAF brevity code token",
    "RAF phonetic words",
    "Ragbaby",
    "Ragbaby ACA classic",
    "Ragbaby ACA word-position v3",
    "Ragbaby keyed alphabet v2",
    "Ragbaby period-word start variant",
    "Ragbaby periodic key ACA v2",
    "Ragbaby word-position classic v4",
    "Rail fence block",
    "Railway Enigma Rocket v2",
    "Random Caesar per letter",
    "Random substitution",
    "Range coder toy token",
    "Raster bits token",
    "RC4 ARCFOUR classic",
    "RC4 hex stream",
    "RC4 keystream token",
    "RC4 stream classic",
    "Reading order route block",
    "Red Book diplomatic code",
    "Red Japanese diplomatic",
    "Red Japanese diplomatic machine",
    "Red machine diplomatic live",
    "Red-Orange Japanese machine style",
    "Reed-Solomon toy syndrome",
    "Regex unicode escape",
    "Regional indicator symbols",
    "Residue vector mod 2-3-5",
    "Resistance book cipher v3",
    "Resistance grille code token",
    "Resistance handkerchief code v2",
    "Resistance handkerchief grid v4",
    "Resistance poem code token",
    "Resistance silk code token",
    "Resistor color code",
    "Reverse alphabet index",
    "Reverse-keyword substitution",
    "RFC1924 Base85 per letter",
    "Rice unary-binary token",
    "RLE binary run token",
    "RLE token",
    "RNA triplet code",
    "Rockex II one-time tape v2",
    "Rockex II tape cipher v5",
    "Rockex II tape style",
    "Rockex one-time tape style",
    "Rockex one-time tape v4",
    "Rockex one-time tape v5",
    "Rockex OTP teleprinter v2",
    "Roman numerals",
    "Rosicrucian cipher classic",
    "Rosicrucian cipher grid v3",
    "Rosicrucian cipher grid v4",
    "Rosicrucian cipher symbols",
    "Rosicrucian dotted grid",
    "Rosicrucian grid classic v2",
    "Rosicrucian nine-chamber cipher",
    "Rosicrucian pigpen variant v3",
    "Rossignol Great Cipher syllables v6",
    "Rossignol Great Cipher table v5",
    "Rossignol homophone table v4",
    "Rossignol syllabic code v3",
    "Rossignol syllable token",
    "Rossignols Great Cipher token",
    "ROT13",
    "ROT18 alpha",
    "ROT18 alphanumeric classic v2",
    "ROT18 Usenet classic v2",
    "ROT47",
    "ROT5 digit companion classic",
    "ROT5 telegraph numeric classic",
    "Rotating square route block",
    "Route cipher block",
    "Route transposition diagonal",
    "Route transposition military",
    "Route transposition rail variant",
    "Route transposition spiral alternate",
    "Rovarspraket",
    "Royal Mail 4-state token",
    "RTTY mark-space token",
    "Ruby hex token",
    "Runic cipher medieval token",
    "Runic cipher twig rune token",
    "Runic substitution medieval elder",
    "Runic substitution younger futhark",
    "Running key book",
    "Running key numeric",
    "Running Key Vigenere",
    "Running-key diplomatic",
    "Running-key field cipher",
    "Russian diplomatic chiffre 1800",
    "Russian diplomatic code 1800s v2",
    "Rust unicode token",
    "Rök runestone shift style",
    "S/KEY one-time password words",
    "Saint-Cyr French army disk v2",
    "Saint-Cyr military slide v4",
    "Saint-Cyr slide",
    "Saint-Cyr slide alphabet v2",
    "Saint-Cyr wheel 1880",
    "Salsa toy token",
    "Samaritan letters",
    "Sans-serif bold italic letters",
    "Sans-serif bold letters",
    "Sans-serif italic letters",
    "Sans-serif letters",
    "Scrabble values",
    "Script letters",
    "Scytale transposition",
    "Semaphore arms",
    "Semaphore compass",
    "Semaphore field flag token",
    "Semaphore flag naval v2",
    "Semaphore flag pair v2",
    "Semaphore naval alphabet 1795",
    "Semaphore naval flag v3",
    "Semaphore text",
    "Seriated Playfair pairs",
    "SGML entity token",
    "SHA1 toy token",
    "SHA256 toy token",
    "Shannon-Fano toy token",
    "Shell ANSI C escape",
    "Siemens T43 one-time tape v2",
    "Siemens T43 tape machine v3",
    "Siemens T52 Geheimschreiber",
    "Siemens T52 Geheimschreiber v4",
    "Siemens T52 Sturgeon style",
    "Siemens T52a live",
    "Siemens T52a Sturgeon v2",
    "Siemens T52a Sturgeon v3",
    "Siemens T52c style live",
    "Siemens T52ca style",
    "Siemens T52d Geheimschreiber v2",
    "Siemens T52d Sturgeon v3",
    "Siemens T52d Sturgeon v4",
    "Siemens T52d style",
    "Siemens T52e live",
    "Siemens T52e Sturgeon v2",
    "Siemens T52e Sturgeon v3",
    "SIGABA cipher maze live",
    "SIGABA CSP-2900 rotor live v2",
    "SIGABA CSP-2900 stepping v3",
    "SIGABA CSP-2900 style",
    "SIGABA CSP-2900 v4",
    "SIGABA CSP-888 style",
    "SIGABA CSP-889 rotor live",
    "SIGABA CSP-889 stepping v2",
    "SIGABA CSP-889 style",
    "SIGABA CSP-889 v4",
    "SIGABA ECM Mark II live",
    "SIGABA index rotor style v2",
    "SIGABA index rotor v3",
    "SIGABA index rotors live",
    "SIGABA rotor live",
    "SIGABA stepping maze style",
    "SIGSALY voice secrecy token",
    "SIGTOT one-time tape style",
    "SIGTOT one-time tape v2",
    "SIGTOT one-time tape v4",
    "Silk code escape map style",
    "Silk code miniature map token",
    "SITOR bit token",
    "Skip permutation block",
    "Slater code 1870 phrase v2",
    "Slater code word variant",
    "Slater telegraph code v2",
    "Slater telegraphic code",
    "Slater telegraphic code v2",
    "Slidefair ACA classic",
    "Slidefair ACA variant v2",
    "Slidefair pairs",
    "SLIDEX battlefield phrase v4",
    "SLIDEX battlefield row-col v3",
    "Slidex message card style",
    "SLIDEX row-column v2",
    "SLIDEX tactical code",
    "SLIDEX tactical phrase board v3",
    "SLIDEX tactical phrase grid v5",
    "SLIDEX tactical phrase v2",
    "Small caps",
    "Snow stego spaces token",
    "SOE one-time pad poem token",
    "SOE poem code field v3",
    "SOE poem code style",
    "SOE poem code transposition",
    "SOE poem code transposition v5",
    "SOE poem transposition v2",
    "SOE poem transposition v4",
    "SOE silk code map v2",
    "SOE silk code token",
    "SOE silk map code v4",
    "SOE silk one-time pad map v3",
    "Solitaire cipher Schneier",
    "Solitaire Pontifex classic",
    "Solitaire/Pontifex",
    "Solresol syllables",
    "Soviet Fialka Cyrillic v4",
    "Soviet Fialka training key v5",
    "Soviet one-time letter pad v3",
    "Soviet one-time pad five-digit",
    "Soviet one-time pad five-letter",
    "Soviet one-time pad token",
    "Soviet OTP five-figure pad v2",
    "Soviet OTP five-figure v3",
    "Soviet OTP five-letter v4",
    "Soviet OTP number station style",
    "Spiral inward route block",
    "Spiral outward route block",
    "Spiral route classic",
    "Spy pencil cipher field v2",
    "SQL CHAR token",
    "Square Caesar shift",
    "Squared A1Z26",
    "Squared unicode letters",
    "St Cyr slide officer key",
    "St. Cyr slide military v3",
    "Standard Galactic tokens",
    "Straddling checkerboard",
    "Straddling checkerboard 0-9 classic",
    "Straddling checkerboard classic",
    "Straddling checkerboard classic v6",
    "Straddling checkerboard decimal variant",
    "Straddling checkerboard Soviet v6",
    "Straddling checkerboard spy v5",
    "STU secure voice token v2",
    "STU-I secure voice token",
    "Subscript letters",
    "Superscript letters",
    "Swagman block",
    "Swiss K commercial Enigma v3",
    "Syriac letters",
    "Tap binary token",
    "Tap code",
    "Tap code 0-based",
    "Tap code binary token v2",
    "Tap code knocks",
    "Tap code Morse token",
    "Tap code row-column words",
    "Telegraph code word",
    "Telepen token",
    "Teleprinter shift token",
    "Templar banking cipher token",
    "Templar cipher cross token v3",
    "Templar cipher symbols",
    "Templar cross alphabet v2",
    "Templar cross cipher alphabet",
    "Templar cross cipher v2",
    "Templar cross cipher v3",
    "Templar cross code",
    "Templar pigpen dotted cross",
    "Temurah cipher token",
    "Ten-code APCO police token",
    "Ten-code APCO police v2",
    "Ten-code APCO public safety v3",
    "Ten-code APCO v4",
    "Ten-code police radio token",
    "Tengwar tokens",
    "Ternary index",
    "TeX alphabet command",
    "TeX char token",
    "Thai alphabet token",
    "The Great Cipher token",
    "Theban alphabet Agrippa v2",
    "Theban tokens",
    "Theban witches alphabet v2",
    "Thue-Morse token",
    "Tifinagh letters",
    "Tironian note token cipher",
    "Tirpitz Enigma K variant v3",
    "TOML unicode token",
    "Tri-Digital ACA cipher",
    "Tri-square triples",
    "Triangular Caesar shift",
    "Triangular numbers",
    "Tridigital ACA checkerboard",
    "Tridigital ACA field cipher v2",
    "Tridigital cipher ACA v3",
    "Tridigital cipher classic",
    "Trifid coordinates",
    "Trifid full period",
    "Trithemius",
    "Trithemius Ave Maria code",
    "Trithemius Ave Maria covertext v4",
    "Trithemius Ave Maria numeric",
    "Trithemius Ave Maria table v2",
    "Trithemius cipher disk",
    "Trithemius descending",
    "Trithemius Polygraphia alphabet",
    "Trithemius Polygraphia Ave Maria v3",
    "Trithemius Polygraphia codeword v2",
    "Trithemius progressive alphabet 1518",
    "Trithemius progressive alphabet v2",
    "Trithemius progressive cipher",
    "Trithemius progressive cipher v4",
    "Trithemius progressive keyed recta",
    "Trithemius progressive Latin v2",
    "Trithemius recta Latin classic",
    "Trithemius Steganographia spirit names",
    "Trithemius tabula recta",
    "Trithemius tabula recta 1508 v2",
    "TSEC/KL-7 token",
    "Tutnese token",
    "Two-hot index token",
    "Two-square 6x6 pairs",
    "Two-square pairs",
    "Two-square vertical pairs",
    "Typex crib-resistant style",
    "Typex Mark 22 style",
    "Typex Mark II five-rotor v3",
    "Typex Mark II live",
    "Typex Mark II plugboard v2",
    "Typex Mark VI rotor order v2",
    "Typex Mark VI rotor v3",
    "Typex Mark VI style",
    "Typex Mark VIII live",
    "Typex Mark VIII rotor style v2",
    "Typex Mark VIII rotor v3",
    "Typex plugboard style live",
    "Typex reflector plugboard style",
    "Typex reflector variant live",
    "Typex rotor live",
    "Ugaritic cuneiform",
    "Unary index",
    "Unicode code point",
    "Unicode decimal code point",
    "Unicode plane token",
    "Union Army cipher disk v2",
    "Union cipher disk",
    "Union cipher wheel v2",
    "Union cipher wheel v3",
    "Union route disk 1860s",
    "Union route transposition",
    "UPC-A check token",
    "Upside-down letters",
    "URI component token",
    "URL form token",
    "URL percent",
    "US Army brevity code token",
    "US Army SIGTOT tape v3",
    "US Army SIGTOT v4",
    "UTF-16BE decimal",
    "UTF-16BE hex",
    "UTF-16LE bytes bracketed",
    "UTF-16LE hex",
    "UTF-32BE hex",
    "UTF-32LE decimal",
    "UTF-32LE hex",
    "UTF-8 binary compact",
    "UTF-8 bytes decimal",
    "UTF-8 bytes hex spaced",
    "UTF-8 C array token",
    "UTF-8 hex",
    "UTF-8 hex colon",
    "UTF-8 octets bracketed",
    "UUencode per letter",
    "UUID byte token",
    "Vanity phone digits",
    "Variant Beaufort",
    "Varicode token",
    "Venetian diplomatic cipher v2",
    "Verhoeff check token",
    "Vernam 1917 Baudot XOR v4",
    "Vernam Baudot 1917 v3",
    "Vernam Baudot tape style",
    "Vernam Baudot XOR field",
    "Vernam Baudot XOR tape v2",
    "Vernam bitmask token",
    "Vernam decimal byte",
    "Vernam mod-26 letters",
    "Vernam one-time tape",
    "Vernam one-time tape v4",
    "Vernam one-time teleprinter tape v3",
    "Vernam teleprinter classic",
    "Vernam teleprinter tape v2",
    "Vernam teleprinter XOR tape v2",
    "Vernam XOR 5-bit",
    "Vertical transposition block",
    "VIC checkerboard",
    "Vigenere",
    "Vowel Caesar",
    "Voynich Currier glyph token",
    "Voynich EVA astronomical page token",
    "Voynich EVA botanical page token",
    "Voynich EVA Currier A token",
    "Voynich EVA Currier B token",
    "Voynich EVA Currier B token v2",
    "Voynich EVA diplomatic",
    "Voynich EVA folio token v3",
    "Voynich EVA glyph style",
    "Voynich EVA token",
    "Voynich EVA transliteration v2",
    "Wabun Japanese Morse token",
    "Wabun Japanese Morse v2",
    "Wabun Japanese Morse v3",
    "Weather code token",
    "Weather ship code token",
    "Weather SYNOP code token",
    "Weather SYNOP five figure v2",
    "Western Union 92 code token",
    "Western Union 92 code v2",
    "Western Union cable code token",
    "Whitespace binary token",
    "Wigwag flag code",
    "Wigwag Myer army signal v2",
    "Wigwag Myer code v2",
    "Wigwag Myer signal v3",
    "Wigwag signal flag Myer code",
    "Wigwag single-flag token",
    "Wingdings tokens",
    "World War I trench code word",
    "Xenocrypt alphabet token",
    "XML CDATA token",
    "XML decimal entity",
    "XML entity decimal padded",
    "XML hex entity",
    "XOR binary with key",
    "XOR checksum token",
    "XOR hex with key",
    "Xorshift stream hex",
    "XXEncode per letter",
    "YAML unicode token",
    "yEnc per letter",
    "Younger Futhark rune cipher v2",
    "Younger Futhark runes",
    "z-base-32 index",
    "Z-code military token",
    "Z-code naval operating signal v2",
    "Z-code naval signal token",
    "Z-code naval signal v3",
    "Z-code naval signal v4",
    "Z-code telegraph token",
    "Z85 index",
    "Z85 per letter",
    "Zalgo light",
    "ZBK Z-code token",
    "Zeckendorf index",
    "Zero padded A1Z26",
    "Zero width binary visible",
    "Zimmermann 13040 codebook v3",
    "Zimmermann cable code variant",
    "Zimmermann code 13040 variant v2",
    "Zimmermann diplomatic code 13040",
    "Zimmermann Telegram code token",
    "Zimmermann telegram code v3",
    "Zimmermann Telegram codebook v2",
    "Zodiac 340 diagonal read style",
    "Zodiac 340 homophonic style",
    "Zodiac 340 route homophonic v4",
    "Zodiac 340 transposition style",
    "Zodiac 340 transposition style v5",
    "Zodiac 340 transposition v6",
    "Zodiac 408 exact-ish style",
    "Zodiac 408 homophonic style",
    "Zodiac 408 homophonic style v5",
    "Zodiac 408 homophonic table v3",
    "Zodiac 408 homophonic v4",
    "Zodiac 408 homophonic v6",
    "Zodiac homophonic 340 style v2",
    "Zodiac symbols",
    "Zstd sequence token"
]

global displayedModeList := MODE_LIST.Clone()

global ROTOR_NAMES := ["I", "II", "III", "IV", "V", "VI", "VII", "VIII"]
global THIN_ROTOR_NAMES := ["Beta", "Gamma"]
global REFLECTOR_M3_NAMES := ["B", "C"]
global REFLECTOR_M4_NAMES := ["B Thin", "C Thin"]

global ROTOR_CATALOG := BuildRotorCatalog()
global REFLECTOR_CATALOG := BuildReflectorCatalog()
global PRESETS_BY_MODE := BuildPresetMap()

global modeName := "Enigma M3"
global enabled := false

global enigmaThin := "Beta"
global enigmaLeft := "I"
global enigmaMiddle := "II"
global enigmaRight := "III"
global enigmaReflector := "B"
global enigmaStart := "AAA"
global enigmaRings := "AAA"
global rotorPositions := StrSplit(enigmaStart)
global plugboardPairs := "AB CD EF"
global plugboard := BuildPlugboard(plugboardPairs)

global shiftValue := 3
global keyText := "LEMON"
global quagPlainKey := "CIPHER"
global quagCipherKey := "MONARCHY"
global quagIndicatorKey := "SECRET"
global quagIndicatorPos := "A"
global affineA := 5
global affineB := 8
global substitutionAlphabet := "QWERTYUIOPASDFGHJKLZXCVBNM"
global outputMode := "Preserve typed case"
global autoResetOnEnable := true
global streamIndex := 0
global autoKeyHistory := ""
global pairBuffer := ""
global condiShift := 0
global chaosLeftDefault := "HXUCZVAMDSLKPEFJRIGTWOBNYQ"
global chaosRightDefault := "PTLNBQDEOYSFAVZKGJRIHWXUMC"
global chaosLeft := chaosLeftDefault
global chaosRight := chaosRightDefault
global solitaireDeck := []
global rc4S := []
global rc4I := 0
global rc4J := 0

; GUI references
global mainGui := ""
global headerText1 := "", headerText2 := "", enableBox := "", autoResetBox := ""
global searchBox := "", modeBox := "", presetBox := "", applyPresetBtn := ""
global settingTitleText := "", settingHintText := ""
global outputModeBox := "", applyBtn := "", resetBtn := "", testBtn := "", quitBtn := ""
global previewInputLabel := "", previewInput := "", previewOutputLabel := "", previewOutput := ""
global statusText := "", stateText := "", hotkeyText := "", noteText := ""
global loadingGui := "", loadingText := "", loadingProgress := ""

global allSettingControls := []
global enigmaPanelControls := []
global enigmaM4OnlyControls := []
global caesarPanelControls := []
global keyPanelControls := []
global affinePanelControls := []
global substitutionPanelControls := []

global thinLabel := "", thinBox := "", leftLabel := "", leftBox := "", middleLabel := "", middleBox := "", rightLabel := "", rightBox := ""
global reflectorLabel := "", reflectorBox := "", startLabel := "", startEdit := "", ringsLabel := "", ringsEdit := "", plugboardLabel := "", plugboardEdit := ""
global shiftLabel := "", shiftEdit := "", keyLabel := "", keyEdit := "", affineALabel := "", affineAEdit := "", affineBLabel := "", affineBEdit := ""
global substitutionLabel := "", substitutionEdit := "", randBtn := ""
global quagmirePanelControls := [], quagPlainControls := [], quagCipherControls := [], quagIndicatorControls := []
global quagPlainLabel := "", quagPlainEdit := "", quagCipherLabel := "", quagCipherEdit := ""
global quagIndicatorLabel := "", quagIndicatorEdit := "", quagPositionLabel := "", quagPositionBox := "", quagHelp := ""

SelfCheckBeforeGuiWithLoading()
BuildGui()
return

; ------------------------------------------------------------
; Hotkeys
; ------------------------------------------------------------

^!e::ToggleEnabledFromHotkey()
^!r::ResetStateFromHotkey()
^!q::ExitApp()

#HotIf IsEncryptionActive()
$a::SendEncrypted("a", false)
$b::SendEncrypted("b", false)
$c::SendEncrypted("c", false)
$d::SendEncrypted("d", false)
$e::SendEncrypted("e", false)
$f::SendEncrypted("f", false)
$g::SendEncrypted("g", false)
$h::SendEncrypted("h", false)
$i::SendEncrypted("i", false)
$j::SendEncrypted("j", false)
$k::SendEncrypted("k", false)
$l::SendEncrypted("l", false)
$m::SendEncrypted("m", false)
$n::SendEncrypted("n", false)
$o::SendEncrypted("o", false)
$p::SendEncrypted("p", false)
$q::SendEncrypted("q", false)
$r::SendEncrypted("r", false)
$s::SendEncrypted("s", false)
$t::SendEncrypted("t", false)
$u::SendEncrypted("u", false)
$v::SendEncrypted("v", false)
$w::SendEncrypted("w", false)
$x::SendEncrypted("x", false)
$y::SendEncrypted("y", false)
$z::SendEncrypted("z", false)

$+a::SendEncrypted("a", true)
$+b::SendEncrypted("b", true)
$+c::SendEncrypted("c", true)
$+d::SendEncrypted("d", true)
$+e::SendEncrypted("e", true)
$+f::SendEncrypted("f", true)
$+g::SendEncrypted("g", true)
$+h::SendEncrypted("h", true)
$+i::SendEncrypted("i", true)
$+j::SendEncrypted("j", true)
$+k::SendEncrypted("k", true)
$+l::SendEncrypted("l", true)
$+m::SendEncrypted("m", true)
$+n::SendEncrypted("n", true)
$+o::SendEncrypted("o", true)
$+p::SendEncrypted("p", true)
$+q::SendEncrypted("q", true)
$+r::SendEncrypted("r", true)
$+s::SendEncrypted("s", true)
$+t::SendEncrypted("t", true)
$+u::SendEncrypted("u", true)
$+v::SendEncrypted("v", true)
$+w::SendEncrypted("w", true)
$+x::SendEncrypted("x", true)
$+y::SendEncrypted("y", true)
$+z::SendEncrypted("z", true)
$Space::SendBoundaryKey(" ")
$Enter::SendBoundaryKey("{Enter}", true)
$Tab::SendBoundaryKey("{Tab}", true)
$Backspace::HandleBackspaceKey()
#HotIf

; ------------------------------------------------------------
; Startup self-check
; ------------------------------------------------------------


SelfCheckBeforeGuiWithLoading() {
    global loadingGui, loadingText, loadingProgress

    loadingGui := Gui("+AlwaysOnTop -MinimizeBox -MaximizeBox", "Cipher GUI loading")
    loadingGui.SetFont("s10")
    loadingGui.AddText("w460", "Starting Cipher GUI")
    loadingText := loadingGui.AddText("w460", "Preparing startup self-check...")
    loadingProgress := loadingGui.AddProgress("w460 h18 Range0-100", 0)
    loadingGui.Show("AutoSize Center")
    Sleep 80

    try {
        SelfCheckBeforeGui()
    } finally {
        TryDestroyLoadingScreen()
    }
}

UpdateLoadingScreen(text, percent := 0) {
    global loadingText, loadingProgress
    try loadingText.Value := text
    try loadingProgress.Value := Max(0, Min(100, percent))
    Sleep 0
}

TryDestroyLoadingScreen() {
    global loadingGui
    try loadingGui.Destroy()
    loadingGui := ""
}

SelfCheckBeforeGui() {
    global MODE_LIST, PRESETS_BY_MODE, modeName, keyText, shiftValue, affineA, affineB, substitutionAlphabet
    global quagPlainKey, quagCipherKey, quagIndicatorKey, quagIndicatorPos

    savedMode := modeName
    savedKey := keyText
    savedShift := shiftValue
    savedA := affineA
    savedB := affineB
    savedSub := substitutionAlphabet
    savedQuagPlain := quagPlainKey
    savedQuagCipher := quagCipherKey
    savedQuagIndicator := quagIndicatorKey
    savedQuagPos := quagIndicatorPos

    problems := ""
    seenModes := Map()

    for idx, checkMode in MODE_LIST {
        if seenModes.Has(checkMode)
            problems .= "Duplicate mode in MODE_LIST: " . checkMode . "`n"
        seenModes[checkMode] := true

        if !PRESETS_BY_MODE.Has(checkMode) {
            problems .= checkMode . ": missing preset list`n"
            continue
        }
        presetList := PRESETS_BY_MODE[checkMode]
        if !IsObject(presetList) || presetList.Length = 0 {
            problems .= checkMode . ": empty or invalid preset list`n"
        } else if presetList[1] != "Custom" {
            problems .= checkMode . ": preset list should start with Custom`n"
        }
    }

    for checkMode, _ in PRESETS_BY_MODE {
        if !seenModes.Has(checkMode)
            problems .= "Preset entry has no matching mode: " . checkMode . "`n"
    }

    sample := "THEQUICKBROWNFOXJUMPSOVERTHELAZYDOGTHEQUICKBROWNFOX"
    totalModes := MODE_LIST.Length
    checkedCount := 0
    for _, testMode in MODE_LIST {
        checkedCount += 1
        if Mod(checkedCount, 10) = 1 || checkedCount = totalModes
            UpdateLoadingScreen("Checking " . checkedCount . "/" . totalModes . ": " . testMode, Floor((checkedCount * 100) / totalModes))
        try {
            PrepareSelfCheckMode(testMode)
            out := ""
            Loop Parse, sample
                out .= EncryptLetterByMode(A_LoopField)
            out .= FlushPendingByMode()
            if out = ""
                problems .= testMode . ": produced empty output for sample input`n"
        } catch Error as e {
            lineText := e.Line ? " line " . e.Line : ""
            problems .= testMode . ":" . lineText . " " . e.Message . "`n"
        }
    }

    modeName := savedMode
    keyText := savedKey
    shiftValue := savedShift
    affineA := savedA
    affineB := savedB
    substitutionAlphabet := savedSub
    quagPlainKey := savedQuagPlain
    quagCipherKey := savedQuagCipher
    quagIndicatorKey := savedQuagIndicator
    quagIndicatorPos := savedQuagPos
    ResetState()

    if problems != "" {
        TryDestroyLoadingScreen()
        fullReport := problems
        shown := LimitLines(fullReport, 40)
        MsgBox "Startup self-check found possible runtime/wiring issues:`n`n" . shown, "Cipher GUI self-check", "Icon!"
    }
}

LimitLines(text, maxLines := 40) {
    out := ""
    count := 0
    Loop Parse, text, "`n", "`r" {
        if A_LoopField = ""
            continue
        count += 1
        if count <= maxLines
            out .= A_LoopField . "`n"
    }
    if count > maxLines
        out .= "... plus " . (count - maxLines) . " more issue(s).`n"
    return out
}

PrepareSelfCheckMode(testMode) {
    global modeName, keyText, shiftValue, affineA, affineB, substitutionAlphabet
    global quagPlainKey, quagCipherKey, quagIndicatorKey, quagIndicatorPos

    modeName := testMode
    keyText := "CIPHER"
    shiftValue := 3
    affineA := 5
    affineB := 8
    substitutionAlphabet := NormalizeSubstitutionAlphabet("QWERTYUIOPASDFGHJKLZXCVBNM")
    quagPlainKey := "CIPHER"
    quagCipherKey := "MONARCHY"
    quagIndicatorKey := "SECRET"
    quagIndicatorPos := "A"

    if testMode = "Gronsfeld" || testMode = "Gronsfeld progressive" || testMode = "Morbit Morse" || testMode = "Gromark" || testMode = "Swagman block"
        keyText := "31415"
    else if testMode = "Bacon biliteral custom"
        keyText := "AB"
    else if testMode = "Double Playfair pairs" || testMode = "Twin Bifid pairs"
        keyText := "ALPHA OMEGA"
    else if testMode = "Hill 3x3 block"
        keyText := "GYBNQKURP"
    else if testMode = "Grandpre coordinate"
        keyText := "CRYPTOGRAPHYALPHABETGRIDMONARCHYSECRET"
    else if testMode = "Bazeries block"
        shiftValue := 31415
    else if testMode = "Rotating square route block"
        shiftValue := 2
    else if testMode = "Route cipher block" || testMode = "Boustrophedon route block" || testMode = "Spiral inward route block" || testMode = "Spiral outward route block"
        shiftValue := 4

    ResetState()
}

; ------------------------------------------------------------
; GUI construction
; ------------------------------------------------------------

BuildGui() {
    global mainGui, headerText1, headerText2, enableBox, autoResetBox, searchBox, modeBox, presetBox, applyPresetBtn
    global settingTitleText, settingHintText, outputModeBox, applyBtn, resetBtn, testBtn, quitBtn
    global previewInputLabel, previewInput, previewOutputLabel, previewOutput, statusText, stateText, hotkeyText, noteText
    global MODE_LIST, displayedModeList, modeName, autoResetOnEnable, enabled

    mainGui := Gui("+AlwaysOnTop +Resize +MinSize900x700", "Live Typing Cipher — v43 category search")
    mainGui.SetFont("s10", "Segoe UI")
    mainGui.MarginX := 16
    mainGui.MarginY := 12

    headerText1 := mainGui.AddText("xm y12 w980", "System-wide live typing cipher")
    headerText2 := mainGui.AddText("xm y36 w980", "Only settings for the selected cipher are visible. Search normally, or use #category, for example #caesar, #polybius, #rotor.")

    enableBox := mainGui.AddCheckBox("xm y76 w160", "Enable now")
    enableBox.Value := enabled ? 1 : 0
    enableBox.OnEvent("Click", EnableClicked)

    autoResetBox := mainGui.AddCheckBox("x190 y76 w240", "Reset state when enabling")
    autoResetBox.Value := autoResetOnEnable ? 1 : 0

    mainGui.AddText("x450 y80 w70", "Search:")
    searchBox := mainGui.AddEdit("x512 y76 w310", "")
    searchBox.OnEvent("Change", SearchChanged)

    mainGui.AddText("xm y116 w90", "Mode:")
    displayedModeList := MODE_LIST.Clone()
    modeBox := mainGui.AddDropDownList("x82 y112 w240", displayedModeList)
    modeBox.Choose(IndexOf(displayedModeList, modeName))
    modeBox.OnEvent("Change", ModeChanged)

    mainGui.AddText("x340 y116 w70", "Preset:")
    presetBox := mainGui.AddDropDownList("x410 y112 w420", GetPresetsForMode(modeName))
    presetBox.OnEvent("Change", PresetChanged)

    applyPresetBtn := mainGui.AddButton("x842 y111 w120", "Apply preset")
    applyPresetBtn.OnEvent("Click", ApplyPresetClicked)

    settingTitleText := mainGui.AddText("xm y154 w980", "Settings")
    settingHintText := mainGui.AddText("xm y178 w980", "")

    BuildSettingsPanels(mainGui)

    mainGui.AddText("xm y320 w90", "Output case:")
    outputModeBox := mainGui.AddDropDownList("x110 y316 w230", ["Preserve typed case", "UPPERCASE", "lowercase"])
    outputModeBox.Choose(1)

    applyBtn := mainGui.AddButton("xm y360 w120", "Apply settings")
    applyBtn.OnEvent("Click", ApplySettingsClicked)

    resetBtn := mainGui.AddButton("x150 y360 w120", "Reset state")
    resetBtn.OnEvent("Click", ResetStateClicked)

    testBtn := mainGui.AddButton("x284 y360 w130", "Encrypt preview")
    testBtn.OnEvent("Click", PreviewClicked)

    quitBtn := mainGui.AddButton("x428 y360 w90", "Quit")
    quitBtn.OnEvent("Click", (*) => ExitApp())

    previewInputLabel := mainGui.AddText("xm y402 w980", "Preview input:")
    previewInput := mainGui.AddEdit("xm y426 w980 h86", "hello world")

    previewOutputLabel := mainGui.AddText("xm y526 w980", "Preview output:")
    previewOutput := mainGui.AddEdit("xm y550 w980 h130 ReadOnly", "")

    statusText := mainGui.AddText("xm y692 w980", "")
    stateText := mainGui.AddText("xm y716 w980", "")
    hotkeyText := mainGui.AddText("xm y748 w980", "Hotkeys: Ctrl+Alt+E toggle | Ctrl+Alt+R reset state | Ctrl+Alt+Q quit")
    noteText := mainGui.AddText("xm y772 w980", "Notes: Random presets generate new settings every time. Some modes output multiple characters per letter. Pair/block modes wait until enough letters are typed, then output a chunk.")

    mainGui.OnEvent("Close", (*) => ExitApp())
    mainGui.OnEvent("Size", GuiResized)

    RefreshPresetList("Custom")
    UpdateModePanel()
    UpdateStatus()
    mainGui.Show("w1040 h830")
}

BuildSettingsPanels(gui) {
    global allSettingControls, enigmaPanelControls, enigmaM4OnlyControls, caesarPanelControls, keyPanelControls, affinePanelControls, substitutionPanelControls, quagmirePanelControls, quagPlainControls, quagCipherControls, quagIndicatorControls
    global thinLabel, thinBox, leftLabel, leftBox, middleLabel, middleBox, rightLabel, rightBox
    global reflectorLabel, reflectorBox, startLabel, startEdit, ringsLabel, ringsEdit, plugboardLabel, plugboardEdit
    global shiftLabel, shiftEdit, keyLabel, keyEdit, affineALabel, affineAEdit, affineBLabel, affineBEdit
    global substitutionLabel, substitutionEdit, randBtn
    global quagPlainLabel, quagPlainEdit, quagCipherLabel, quagCipherEdit, quagIndicatorLabel, quagIndicatorEdit, quagPositionLabel, quagPositionBox, quagHelp
    global ROTOR_NAMES, THIN_ROTOR_NAMES, REFLECTOR_M3_NAMES, ALPHABET

    ; Controls are placed in the same clean settings zone.
    ; Irrelevant controls are hidden, but their positions never overlap the header row.
    baseY := 208

    ; Enigma panel, row 1
    thinLabel := gui.AddText("xm y" baseY " w70", "Thin rotor:")
    thinBox := gui.AddDropDownList("x92 y" (baseY - 4) " w110", THIN_ROTOR_NAMES)
    thinBox.Choose(1)

    leftLabel := gui.AddText("x220 y" baseY " w45", "Left:")
    leftBox := gui.AddDropDownList("x266 y" (baseY - 4) " w90", ROTOR_NAMES)
    leftBox.Choose(1)

    middleLabel := gui.AddText("x374 y" baseY " w60", "Middle:")
    middleBox := gui.AddDropDownList("x438 y" (baseY - 4) " w90", ROTOR_NAMES)
    middleBox.Choose(2)

    rightLabel := gui.AddText("x546 y" baseY " w50", "Right:")
    rightBox := gui.AddDropDownList("x600 y" (baseY - 4) " w90", ROTOR_NAMES)
    rightBox.Choose(3)

    ; Enigma panel, row 2
    reflectorLabel := gui.AddText("xm y246 w70", "Reflector:")
    reflectorBox := gui.AddDropDownList("x92 y242 w150", REFLECTOR_M3_NAMES)
    reflectorBox.Choose(1)

    startLabel := gui.AddText("x270 y246 w78", "Start pos:")
    startEdit := gui.AddEdit("x350 y242 w110 Uppercase", "AAA")

    ringsLabel := gui.AddText("x488 y246 w55", "Rings:")
    ringsEdit := gui.AddEdit("x548 y242 w110 Uppercase", "AAA")

    ; Enigma panel, row 3
    plugboardLabel := gui.AddText("xm y284 w80", "Plugboard:")
    plugboardEdit := gui.AddEdit("x92 y280 w720", "AB CD EF")

    enigmaPanelControls := [thinLabel, thinBox, leftLabel, leftBox, middleLabel, middleBox, rightLabel, rightBox, reflectorLabel, reflectorBox, startLabel, startEdit, ringsLabel, ringsEdit, plugboardLabel, plugboardEdit]
    enigmaM4OnlyControls := [thinLabel, thinBox]

    ; Caesar panel
    shiftLabel := gui.AddText("xm y" baseY " w90", "Shift:")
    shiftEdit := gui.AddEdit("x110 y" (baseY - 4) " w110", "3")
    shiftHelp := gui.AddText("x240 y" baseY " w620", "Used by Caesar. Negative values work, e.g. -3.")
    caesarPanelControls := [shiftLabel, shiftEdit, shiftHelp]

    ; Key panel
    keyLabel := gui.AddText("xm y" baseY " w90", "Key:")
    keyEdit := gui.AddEdit("x110 y" (baseY - 4) " w500", "LEMON")
    keyHelp := gui.AddText("xm y246 w860", "Used by Vigenere, Autokey Vigenere, Beaufort, Porta, and Keyword substitution.")
    keyPanelControls := [keyLabel, keyEdit, keyHelp]

    ; Quagmire panel
    quagPlainLabel := gui.AddText("xm y" baseY " w130", "Plain alphabet key:")
    quagPlainEdit := gui.AddEdit("x150 y" (baseY - 4) " w230 Uppercase", "CIPHER")
    quagCipherLabel := gui.AddText("x410 y" baseY " w135", "Cipher alphabet key:")
    quagCipherEdit := gui.AddEdit("x552 y" (baseY - 4) " w230 Uppercase", "MONARCHY")
    quagIndicatorLabel := gui.AddText("xm y246 w130", "Indicator key:")
    quagIndicatorEdit := gui.AddEdit("x150 y242 w230 Uppercase", "SECRET")
    quagPositionLabel := gui.AddText("x410 y246 w135", "Indicator pos:")
    quagPositionBox := gui.AddDropDownList("x552 y242 w90", StrSplit(ALPHABET))
    quagPositionBox.Choose(1)
    quagHelp := gui.AddText("xm y284 w920", "Quagmire uses an indicator key plus mixed alphabet keys. Quagmire IV uses separate plaintext and ciphertext alphabet keys.")
    quagPlainControls := [quagPlainLabel, quagPlainEdit]
    quagCipherControls := [quagCipherLabel, quagCipherEdit]
    quagIndicatorControls := [quagIndicatorLabel, quagIndicatorEdit, quagPositionLabel, quagPositionBox]
    quagmirePanelControls := [quagPlainLabel, quagPlainEdit, quagCipherLabel, quagCipherEdit, quagIndicatorLabel, quagIndicatorEdit, quagPositionLabel, quagPositionBox, quagHelp]

    ; Affine panel
    affineALabel := gui.AddText("xm y" baseY " w90", "Affine a:")
    affineAEdit := gui.AddEdit("x110 y" (baseY - 4) " w100", "5")
    affineBLabel := gui.AddText("x240 y" baseY " w80", "Affine b:")
    affineBEdit := gui.AddEdit("x326 y" (baseY - 4) " w100", "8")
    affineHelp := gui.AddText("xm y246 w860", "a must be coprime with 26: 1, 3, 5, 7, 9, 11, 15, 17, 19, 21, 23, 25.")
    affinePanelControls := [affineALabel, affineAEdit, affineBLabel, affineBEdit, affineHelp]

    ; Substitution panel
    substitutionLabel := gui.AddText("xm y" baseY " w100", "Sub alphabet:")
    substitutionEdit := gui.AddEdit("x110 y" (baseY - 4) " w600 Uppercase", "QWERTYUIOPASDFGHJKLZXCVBNM")
    randBtn := gui.AddButton("x724 y" (baseY - 5) " w110", "Randomize")
    randBtn.OnEvent("Click", RandomizeSubstitutionClicked)
    substitutionHelp := gui.AddText("xm y246 w860", "Used by Random substitution only. The alphabet is normalized to 26 unique letters.")
    substitutionPanelControls := [substitutionLabel, substitutionEdit, randBtn, substitutionHelp]

    allSettingControls := []
    for _, list in [enigmaPanelControls, caesarPanelControls, keyPanelControls, quagmirePanelControls, affinePanelControls, substitutionPanelControls] {
        for _, ctrl in list
            allSettingControls.Push(ctrl)
    }
}

GuiResized(thisGui, minMax, width, height) {
    global headerText1, headerText2, settingTitleText, settingHintText, searchBox, presetBox, applyPresetBtn
    global plugboardEdit, keyEdit, substitutionEdit, randBtn
    global previewInputLabel, previewInput, previewOutputLabel, previewOutput, statusText, stateText, hotkeyText, noteText

    if minMax = -1
        return

    contentW := Max(620, width - 32)

    TryMoveWidth(headerText1, contentW)
    TryMoveWidth(headerText2, contentW)
    TryMoveWidth(settingTitleText, contentW)
    TryMoveWidth(settingHintText, contentW)
    TryMoveWidth(previewInputLabel, contentW)
    TryMoveWidth(previewOutputLabel, contentW)

    ; Keep the preset row compact. Do not stretch the preset box across the whole screen.
    presetW := Min(620, Max(300, width - 550))
    try presetBox.Move(410, 112, presetW, 24)
    try applyPresetBtn.Move(410 + presetW + 12, 111, 120, 26)

    ; Stretch only the long text fields.
    TryMoveWidth(plugboardEdit, Max(400, width - 132))
    TryMoveWidth(keyEdit, Max(320, width - 540))
    subW := Max(320, width - 300)
    TryMoveWidth(substitutionEdit, subW)
    TryMoveX(randBtn, 110 + subW + 14)

    TryMoveWidth(previewInput, contentW)
    try previewInput.Move(16, 426, contentW, 86)

    try previewOutput.GetPos(&outX, &outY, &outW, &outH)
    catch
        return

    newOutH := Max(90, height - outY - 150)
    previewOutput.Move(16, outY, contentW, newOutH)

    statusY := outY + newOutH + 10
    statusText.Move(16, statusY, contentW, 22)
    stateText.Move(16, statusY + 24, contentW, 22)
    hotkeyText.Move(16, statusY + 56, contentW, 22)
    noteText.Move(16, statusY + 80, contentW, 38)
}

TryMoveWidth(ctrl, width) {
    try {
        ctrl.GetPos(&x, &y, &w, &h)
        ctrl.Move(x, y, width, h)
    }
}

TryMoveX(ctrl, x) {
    try {
        ctrl.GetPos(&oldX, &y, &w, &h)
        ctrl.Move(x, y, w, h)
    }
}

; ------------------------------------------------------------
; Presets
; ------------------------------------------------------------

BuildPresetMap() {
    global MODE_LIST
    m := Map()
    m["Enigma M3"] := [
        "Custom",
        "M3 — Army default I-II-III B AAA",
        "M3 — no plugboard AAA",
        "M3 — no plugboard ZZZ",
        "M3 — strong plugboard DOG",
        "M3 — training AAB",
        "M3 — message key CAT",
        "M3 — midnight MCK",
        "M3 — Bletchley style",
        "M3 — naval style I-II-V",
        "M3 — rotor IV-V-I",
        "M3 — rotor V-III-II",
        "M3 — turnover test VEV",
        "M3 — rings BCD",
        "M3 — rings MCK",
        "M3 — alphabet pairs",
        "M3 — random preset 1",
        "M3 — random preset 2",
        "M3 — random preset 3",
        "M3 — random plugboard",
        "M3 — random full machine"
    ]
    m["Enigma M4"] := [
        "Custom",
        "M4 — Beta I-II-III B Thin AAAA",
        "M4 — Gamma I-II-III C Thin AAAA",
        "M4 — no plugboard ZZZZ",
        "M4 — naval U-boat 1",
        "M4 — naval U-boat 2",
        "M4 — Triton style",
        "M4 — Beta IV-V-II",
        "M4 — Gamma VIII-VI-III",
        "M4 — message key WAVE",
        "M4 — message key BOAT",
        "M4 — rings AAAA",
        "M4 — rings BETA",
        "M4 — rings MARS",
        "M4 — thin Beta strong plugboard",
        "M4 — thin Gamma strong plugboard",
        "M4 — random preset 1",
        "M4 — random preset 2",
        "M4 — random preset 3",
        "M4 — random plugboard",
        "M4 — random full machine"
    ]
    m["Caesar"] := ["Custom", "Caesar +1", "Caesar +2", "Caesar +3", "Caesar +5", "Caesar +7", "Caesar +13", "Caesar -1", "Caesar -3", "Caesar -5", "Caesar +19", "Caesar -19", "Caesar random"]
    m["Progressive Caesar"] := ["Custom", "Progressive Caesar start 0", "Progressive Caesar start 3", "Progressive Caesar random start"]
    m["Trithemius"] := ["Custom", "Trithemius start 0", "Trithemius start 1", "Trithemius random start"]
    m["ROT13"] := ["Custom", "ROT13"]
    m["Atbash"] := ["Custom", "Atbash"]
    m["Vigenere"] := ["Custom", "Vigenere — LEMON", "Vigenere — DRAGON", "Vigenere — CIPHER", "Vigenere — SHADOW", "Vigenere — ORANGE", "Vigenere — MONARCHY", "Vigenere — ENIGMA", "Vigenere — SECRET", "Vigenere — random key"]
    m["Autokey Vigenere"] := ["Custom", "Autokey — QUEENLY", "Autokey — CIPHER", "Autokey — DRAGON", "Autokey — MONARCHY", "Autokey — SECRET", "Autokey — random key"]
    m["Gronsfeld"] := ["Custom", "Gronsfeld — 31415", "Gronsfeld — 27182", "Gronsfeld — 12345", "Gronsfeld — random digits"]
    m["Running Key Vigenere"] := ["Custom", "Running key — THEQUICKBROWNFOX", "Running key — CRYPTOGRAPHY", "Running key — random long key"]
    m["Beaufort"] := ["Custom", "Beaufort — FORT", "Beaufort — KEY", "Beaufort — CIPHER", "Beaufort — LEMON", "Beaufort — ENIGMA", "Beaufort — random key"]
    m["Variant Beaufort"] := ["Custom", "Variant Beaufort — FORT", "Variant Beaufort — KEY", "Variant Beaufort — CIPHER", "Variant Beaufort — random key"]
    m["Porta"] := ["Custom", "Porta — PORTA", "Porta — KEY", "Porta — CIPHER", "Porta — DRAGON", "Porta — SECRET", "Porta — random key"]
    m["Affine"] := ["Custom", "Affine 1,13", "Affine 3,7", "Affine 5,8", "Affine 7,3", "Affine 11,6", "Affine 17,20", "Affine 25,25", "Affine random"]
    m["Keyword substitution"] := ["Custom", "Keyword — CIPHER", "Keyword — QWERTY", "Keyword — ZEBRAS", "Keyword — MONARCHY", "Keyword — SECRET", "Keyword — DRAGON", "Keyword — ENIGMA", "Keyword — random key"]
    m["Random substitution"] := ["Custom", "Random substitution — random 1", "Random substitution — random 2", "Random substitution — random 3", "Random substitution — random now", "Random substitution — QWERTY fixed", "Random substitution — reverse fixed"]
    m["QWERTY to Dvorak"] := ["Custom", "QWERTY to Dvorak"]
    m["QWERTY to AZERTY"] := ["Custom", "QWERTY to AZERTY"]
    m["Keyboard mirror"] := ["Custom", "Keyboard mirror rows"]
    m["Leet basic"] := ["Custom", "Leet basic"]
    m["Morse letters"] := ["Custom", "Morse letters"]
    m["Binary 5-bit"] := ["Custom", "Binary 5-bit"]
    m["Baconian A/B"] := ["Custom", "Baconian A/B"]
    m["A1Z26 numbers"] := ["Custom", "A1Z26 numbers"]
    m["Polybius square"] := ["Custom", "Polybius square"]
    m["Tap code"] := ["Custom", "Tap code"]
    m["ADFGX"] := ["Custom", "ADFGX"]
    m["ADFGVX"] := ["Custom", "ADFGVX"]
    m["Straddling checkerboard"] := ["Custom", "Straddling checkerboard"]
    m["Monome-Dinome"] := ["Custom", "Monome-Dinome"]
    m["Pollux Morse"] := ["Custom", "Pollux Morse — random digits"]
    m["Base64 per letter"] := ["Custom", "Base64 per letter"]
    m["URL percent"] := ["Custom", "URL percent"]
    m["HTML entity"] := ["Custom", "HTML entity"]
    m["Unicode code point"] := ["Custom", "Unicode code point"]
    m["ASCII binary 8-bit"] := ["Custom", "ASCII binary 8-bit"]
    m["XOR hex with key"] := ["Custom", "XOR hex — KEY", "XOR hex — SECRET", "XOR hex — random key"]
    m["XOR binary with key"] := ["Custom", "XOR binary — KEY", "XOR binary — SECRET", "XOR binary — random key"]
    m["Braille"] := ["Custom", "Braille"]
    m["Pigpen symbols"] := ["Custom", "Pigpen symbols"]
    m["Emoji alphabet"] := ["Custom", "Emoji alphabet"]
    m["Letter index hex"] := ["Custom", "Letter index hex"]
    m["Roman numerals"] := ["Custom", "Roman numerals"]
    m["Prime numbers"] := ["Custom", "Prime numbers"]
    m["Squared A1Z26"] := ["Custom", "Squared A1Z26"]
    m["Condi"] := ["Custom", "Condi — CIPHER", "Condi — KEYWORD", "Condi — random key"]
    m["Chaocipher"] := ["Custom", "Chaocipher default"]
    m["Playfair pairs"] := ["Custom", "Playfair — MONARCHY", "Playfair — CIPHER", "Playfair — SECRET", "Playfair — random key"]
    m["Hill 2x2 pairs"] := ["Custom", "Hill 2x2 — fixed matrix"]
    m["Bifid pairs"] := ["Custom", "Bifid — MONARCHY", "Bifid — CIPHER", "Bifid — SECRET", "Bifid — random key"]
    m["Two-square pairs"] := ["Custom", "Two-square — CIPHER", "Two-square — MONARCHY", "Two-square — random key"]
    m["Four-square pairs"] := ["Custom", "Four-square — CIPHER", "Four-square — MONARCHY", "Four-square — random key"]
    m["Nihilist substitution"] := ["Custom", "Nihilist — CIPHER", "Nihilist — MONARCHY", "Nihilist — random key"]
    m["Trifid coordinates"] := ["Custom", "Trifid coordinates"]
    m["Checkerboard coordinates"] := ["Custom", "Checkerboard coordinates"]
    m["Baudot ITA2"] := ["Custom", "Baudot ITA2"]
    m["Gray code 5-bit"] := ["Custom", "Gray code 5-bit"]
    m["BCD A1Z26"] := ["Custom", "BCD A1Z26"]
    m["Fibonacci numbers"] := ["Custom", "Fibonacci numbers"]
    m["Triangular numbers"] := ["Custom", "Triangular numbers"]
    m["Cubed A1Z26"] := ["Custom", "Cubed A1Z26"]
    m["Factorial index"] := ["Custom", "Factorial index"]
    m["Modulo 9 index"] := ["Custom", "Modulo 9 index"]
    m["Reverse alphabet index"] := ["Custom", "Reverse alphabet index"]
    m["Keyboard Caesar"] := ["Custom", "Keyboard Caesar +1", "Keyboard Caesar +3", "Keyboard Caesar random"]
    m["Vowel Caesar"] := ["Custom", "Vowel Caesar +1", "Vowel Caesar +2", "Vowel Caesar random"]
    m["Consonant Caesar"] := ["Custom", "Consonant Caesar +1", "Consonant Caesar +5", "Consonant Caesar random"]
    m["Alternating Caesar"] := ["Custom", "Alternating Caesar +3", "Alternating Caesar +7", "Alternating Caesar random"]
    m["Elder Futhark runes"] := ["Custom", "Elder Futhark runes"]
    m["Ogham letters"] := ["Custom", "Ogham letters"]
    m["Semaphore text"] := ["Custom", "Semaphore text"]
    m["Masonic pigpen variant"] := ["Custom", "Masonic pigpen variant"]
    m["Progressive Vigenere"] := ["Custom", "Progressive Vigenere — LEMON", "Progressive Vigenere — CIPHER", "Progressive Vigenere — random key"]
    m["Quagmire I"] := ["Custom", "Quagmire I — plain CIPHER indicator SECRET", "Quagmire I — plain MONARCHY indicator SEARCH", "Quagmire I — random"]
    m["Quagmire II"] := ["Custom", "Quagmire II — cipher CIPHER indicator SECRET", "Quagmire II — cipher MONARCHY indicator SEARCH", "Quagmire II — random"]
    m["Quagmire III"] := ["Custom", "Quagmire III — alphabet CIPHER indicator SECRET", "Quagmire III — alphabet MONARCHY indicator SEARCH", "Quagmire III — random"]
    m["Quagmire IV"] := ["Custom", "Quagmire IV — plain CIPHER cipher MONARCHY indicator SECRET", "Quagmire IV — plain KRYPTOS cipher PALIMPSEST indicator ABSCISSA", "Quagmire IV — random"]
    m["Alberti disk"] := ["Custom", "Alberti — CIPHER", "Alberti — MONARCHY", "Alberti — random key"]
    m["Bellaso"] := ["Custom", "Bellaso — LEMON", "Bellaso — CIPHER", "Bellaso — random key"]
    m["Autokey Beaufort"] := ["Custom", "Autokey Beaufort — FORT", "Autokey Beaufort — CIPHER", "Autokey Beaufort — random key"]
    m["Progressive Porta"] := ["Custom", "Progressive Porta — PORTA", "Progressive Porta — CIPHER", "Progressive Porta — random key"]
    m["Gronsfeld progressive"] := ["Custom", "Gronsfeld progressive — 31415", "Gronsfeld progressive — 27182", "Gronsfeld progressive — random digits"]
    m["Keyed Atbash"] := ["Custom", "Keyed Atbash — CIPHER", "Keyed Atbash — MONARCHY", "Keyed Atbash — random key"]
    m["Diana cipher"] := ["Custom", "Diana — SECRET", "Diana — LEMON", "Diana — random key"]
    m["Random Caesar per letter"] := ["Custom", "Random Caesar per letter"]
    m["Fibonacci Caesar shift"] := ["Custom", "Fibonacci Caesar shift"]
    m["Prime Caesar shift"] := ["Custom", "Prime Caesar shift"]
    m["Homophonic numbers"] := ["Custom", "Homophonic numbers — random"]
    m["Base32 per letter"] := ["Custom", "Base32 per letter"]
    m["Quoted printable"] := ["Custom", "Quoted printable"]
    m["Decimal A0Z25"] := ["Custom", "Decimal A0Z25"]
    m["Zero padded A1Z26"] := ["Custom", "Zero padded A1Z26"]
    m["Octal A1Z26"] := ["Custom", "Octal A1Z26"]
    m["Binary 6-bit index"] := ["Custom", "Binary 6-bit index"]
    m["Coordinate 0-based"] := ["Custom", "Coordinate 0-based"]
    m["Morse compact 01"] := ["Custom", "Morse compact 01"]
    m["Polybius reversed"] := ["Custom", "Polybius reversed"]
    m["Maritime signal flags"] := ["Custom", "Maritime signal flags"]
    m["Regional indicator symbols"] := ["Custom", "Regional indicator symbols"]
    m["Circled letters"] := ["Custom", "Circled letters"]
    m["Squared unicode letters"] := ["Custom", "Squared unicode letters"]
    m["Parenthesized letters"] := ["Custom", "Parenthesized letters"]
    m["Fraktur letters"] := ["Custom", "Fraktur letters"]
    m["Script letters"] := ["Custom", "Script letters"]
    m["Small caps"] := ["Custom", "Small caps"]
    m["Superscript letters"] := ["Custom", "Superscript letters"]
    m["Subscript letters"] := ["Custom", "Subscript letters"]
    m["Zalgo light"] := ["Custom", "Zalgo light — random marks"]
    m["Mirror text alphabet"] := ["Custom", "Mirror text alphabet"]
    m["Keyed Polybius square"] := ["Custom", "Keyed Polybius — CIPHER", "Keyed Polybius — MONARCHY", "Keyed Polybius — random key"]
    m["Keyed ADFGX"] := ["Custom", "Keyed ADFGX — CIPHER", "Keyed ADFGX — PHQG", "Keyed ADFGX — random key"]
    m["Keyed ADFGVX"] := ["Custom", "Keyed ADFGVX — CIPHER", "Keyed ADFGVX — NUMBERS", "Keyed ADFGVX — random key"]
    m["Morbit Morse"] := ["Custom", "Morbit — 123456789", "Morbit — random digits"]
    m["Fractionated Morse"] := ["Custom", "Fractionated Morse — CIPHER", "Fractionated Morse — SECRET", "Fractionated Morse — random key"]
    m["Morse reverse"] := ["Custom", "Morse reverse"]
    m["Morse emoji"] := ["Custom", "Morse emoji"]
    m["Morse tap digits"] := ["Custom", "Morse tap digits"]
    m["Baconian 24 I/J"] := ["Custom", "Baconian 24 I/J"]
    m["Kamasutra substitution"] := ["Custom", "Kamasutra — alphabet halves", "Kamasutra — CIPHER", "Kamasutra — random key"]
    m["Phillips cipher"] := ["Custom", "Phillips — PHILLIPS", "Phillips — CIPHER", "Phillips — random key"]
    m["Slidefair pairs"] := ["Custom", "Slidefair — SLIDE", "Slidefair — CIPHER", "Slidefair — random key"]
    m["Colemak keyboard"] := ["Custom", "Colemak keyboard"]
    m["QWERTZ keyboard"] := ["Custom", "QWERTZ keyboard"]
    m["Keyboard adjacent right"] := ["Custom", "Keyboard adjacent right"]
    m["Keyboard adjacent left"] := ["Custom", "Keyboard adjacent left"]
    m["Phone T9 digit"] := ["Custom", "Phone T9 digit"]
    m["Phone multitap"] := ["Custom", "Phone multitap"]
    m["Chess coordinates"] := ["Custom", "Chess coordinates"]
    m["Dice pair code"] := ["Custom", "Dice pair code"]
    m["Domino tile code"] := ["Custom", "Domino tile code"]
    m["Playing card code"] := ["Custom", "Playing card code"]
    m["Base58 index"] := ["Custom", "Base58 index"]
    m["Base62 index"] := ["Custom", "Base62 index"]
    m["Crockford Base32 index"] := ["Custom", "Crockford Base32 index"]
    m["Base85 per letter"] := ["Custom", "Base85 per letter"]
    m["UUencode per letter"] := ["Custom", "UUencode per letter"]
    m["EBCDIC hex"] := ["Custom", "EBCDIC hex"]
    m["UTF-8 hex"] := ["Custom", "UTF-8 hex"]
    m["UTF-16LE hex"] := ["Custom", "UTF-16LE hex"]
    m["HTML hex entity"] := ["Custom", "HTML hex entity"]
    m["LCG checksum token"] := ["Custom", "LCG checksum token"]
    m["Knuth checksum token"] := ["Custom", "Knuth checksum token"]
    m["Hex ASCII"] := ["Custom", "Hex ASCII"]
    m["ASCII decimal"] := ["Custom", "ASCII decimal"]
    m["Octal ASCII"] := ["Custom", "Octal ASCII"]
    m["Fullwidth letters"] := ["Custom", "Fullwidth letters"]
    m["Upside-down letters"] := ["Custom", "Upside-down letters"]
    m["Greek lookalike"] := ["Custom", "Greek lookalike"]
    m["Cyrillic lookalike"] := ["Custom", "Cyrillic lookalike"]
    m["NATO words"] := ["Custom", "NATO words"]
    m["Rail fence block"] := ["Custom", "Rail fence — rails 3", "Rail fence — rails 4", "Rail fence — random rails"]
    m["Scytale transposition"] := ["Custom", "Scytale — width 4", "Scytale — width 5", "Scytale — random width"]
    m["Columnar transposition block"] := ["Custom", "Columnar — ZEBRAS", "Columnar — CARGO", "Columnar — SECRET", "Columnar — random key"]
    m["Double columnar block"] := ["Custom", "Double columnar — ZEBRAS", "Double columnar — CARGO", "Double columnar — random key"]
    m["Route cipher block"] := ["Custom", "Route cipher — 3x3 spiral", "Route cipher — 4x4 spiral"]
    m["Myszkowski transposition block"] := ["Custom", "Myszkowski — BALLOON", "Myszkowski — MISSISSIPPI", "Myszkowski — random key"]
    m["Jefferson disk"] := ["Custom", "Jefferson — CIPHER", "Jefferson — PRESIDENT", "Jefferson — random key"]
    m["M-94 cylinder style"] := ["Custom", "M-94 — CIPHER", "M-94 — ARMY", "M-94 — random key"]
    m["Bazeries cylinder style"] := ["Custom", "Bazeries — CIPHER", "Bazeries — FRANCE", "Bazeries — random key"]
    m["M-209 Hagelin style"] := ["Custom", "M-209 — default pins", "M-209 — random start"]
    m["VIC checkerboard"] := ["Custom", "VIC checkerboard — ETAOIN", "VIC checkerboard — CIPHER", "VIC checkerboard — random key"]
    m["One-time pad A-Z"] := ["Custom", "OTP — LEMON", "OTP — SECRET", "OTP — random pad"]
    m["Vernam XOR 5-bit"] := ["Custom", "Vernam — LEMON", "Vernam — SECRET", "Vernam — random key"]
    m["RC4 hex stream"] := ["Custom", "RC4 — KEY", "RC4 — SECRET", "RC4 — random key"]
    m["Solitaire/Pontifex"] := ["Custom", "Solitaire — SECRET", "Solitaire — CRYPTO", "Solitaire — random key"]
    m["Bifid full period"] := ["Custom", "Bifid full — MONARCHY", "Bifid full — CIPHER", "Bifid full — random key"]
    m["Trifid full period"] := ["Custom", "Trifid full — TRIFID", "Trifid full — CIPHER", "Trifid full — random key"]
    m["Nihilist numeric stream"] := ["Custom", "Nihilist numeric — CIPHER", "Nihilist numeric — MONARCHY", "Nihilist numeric — random key"]
    m["Book cipher index"] := ["Custom", "Book cipher — NATO", "Book cipher — POE", "Book cipher — random book key"]
    m["Ragbaby"] := ["Custom", "Ragbaby — RAGBABY", "Ragbaby — CIPHER", "Ragbaby — random key"]
    m["Nicodemus block"] := ["Custom", "Nicodemus — NICODEMUS", "Nicodemus — CIPHER", "Nicodemus — random key"]
    m["Clave"] := ["Custom", "Clave — CLAVE", "Clave — CIPHER", "Clave — random key"]
    m["Gromark"] := ["Custom", "Gromark — primer 12345", "Gromark — CIPHER", "Gromark — random primer"]
    m["Seriated Playfair pairs"] := ["Custom", "Seriated Playfair — KEYWORD", "Seriated Playfair — MONARCHY", "Seriated Playfair — random key"]
    m["Playfair 6x6 pairs"] := ["Custom", "Playfair 6x6 — KEYWORD", "Playfair 6x6 — NUMBERS", "Playfair 6x6 — random key"]
    m["Two-square vertical pairs"] := ["Custom", "Two-square vertical — EXAMPLE", "Two-square vertical — CIPHER", "Two-square vertical — random key"]
    m["Tri-square triples"] := ["Custom", "Tri-square — ALPHA", "Tri-square — CIPHER", "Tri-square — random key"]
    m["Two-square 6x6 pairs"] := ["Custom", "Two-square 6x6 — EXAMPLE", "Two-square 6x6 — CIPHER", "Two-square 6x6 — random key"]
    m["Four-square 6x6 pairs"] := ["Custom", "Four-square 6x6 — EXAMPLE", "Four-square 6x6 — CIPHER", "Four-square 6x6 — random key"]
    m["Bifid 6x6 pairs"] := ["Custom", "Bifid 6x6 — KEYWORD", "Bifid 6x6 — CIPHER", "Bifid 6x6 — random key"]
    m["Hill 3x3 block"] := ["Custom", "Hill 3x3 — classic", "Hill 3x3 — random start"]
    m["Cadenus block"] := ["Custom", "Cadenus — CADENUS", "Cadenus — CIPHER", "Cadenus — random key"]
    m["AMSCO block"] := ["Custom", "AMSCO — CIPHER", "AMSCO — ZEBRAS", "AMSCO — random key"]
    m["Swagman block"] := ["Custom", "Swagman — 3142", "Swagman — 2413", "Swagman — random digits"]
    m["Bazeries block"] := ["Custom", "Bazeries — BAZERIES 31415", "Bazeries — CIPHER 27182", "Bazeries — random"]
    m["Disrupted transposition block"] := ["Custom", "Disrupted — DISRUPT", "Disrupted — CIPHER", "Disrupted — random key"]
    m["Incomplete columnar block"] := ["Custom", "Incomplete columnar — CIPHER", "Incomplete columnar — ZEBRAS", "Incomplete columnar — random key"]
    m["Complete columnar block"] := ["Custom", "Complete columnar — CIPHER", "Complete columnar — ZEBRAS", "Complete columnar — random key"]
    m["Alternating columnar block"] := ["Custom", "Alternating columnar — CIPHER", "Alternating columnar — ZEBRAS", "Alternating columnar — random key"]
    m["Boustrophedon route block"] := ["Custom", "Boustrophedon — 4x4", "Boustrophedon — 5x5"]
    m["Spiral inward route block"] := ["Custom", "Spiral inward — 4x4", "Spiral inward — 5x5"]
    m["Spiral outward route block"] := ["Custom", "Spiral outward — 4x4", "Spiral outward — 5x5"]
    m["Reading order route block"] := ["Custom", "Reading route — columns", "Reading route — boustrophedon"]
    m["Rotating square route block"] := ["Custom", "Rotating square — 90", "Rotating square — 180", "Rotating square — random"]
    m["Grille mask block"] := ["Custom", "Grille mask — diagonal", "Grille mask — sparse"]
    m["Fleissner grille block"] := ["Custom", "Fleissner — 4x4 sample"]
    m["Homophonic substitution"] := ["Custom", "Homophonic substitution"]
    m["ADFGVX escaped"] := ["Custom", "ADFGVX escaped — KEYW0RD", "ADFGVX escaped — random key"]
    m["Base45 per letter"] := ["Custom", "Base45 per letter"]
    m["Base36 per letter"] := ["Custom", "Base36 per letter"]
    m["Base92 per letter"] := ["Custom", "Base92 per letter"]
    m["Z85 per letter"] := ["Custom", "Z85 per letter"]

    m["ROT47"] := ["Custom", "ROT47"]
    m["Caesar custom alphabet"] := ["Custom", "Custom alphabet — QWERTY +3", "Custom alphabet — random +3"]
    m["Della Porta disk"] := ["Custom", "Della Porta — CIPHER", "Della Porta — MONARCHY", "Della Porta — random key"]
    m["Lorenz SZ40 toy stream"] := ["Custom", "Lorenz — LORENZ", "Lorenz — SECRET", "Lorenz — random seed"]
    m["Hagelin C-series toy stream"] := ["Custom", "Hagelin — HAGELIN", "Hagelin — SECRET", "Hagelin — random seed"]
    m["Redefence rail offset block"] := ["Custom", "Redefence — rails 3", "Redefence — rails 4", "Redefence — random rails"]
    m["Playfair Q omitted pairs"] := ["Custom", "Playfair Q omitted — KEYWORD", "Playfair Q omitted — MONARCHY", "Playfair Q omitted — random key"]
    m["Double Playfair pairs"] := ["Custom", "Double Playfair — ALPHA/OMEGA", "Double Playfair — CIPHER", "Double Playfair — random key"]
    m["Twin Bifid pairs"] := ["Custom", "Twin Bifid — ALPHA/OMEGA", "Twin Bifid — CIPHER", "Twin Bifid — random key"]
    m["Polybius columnar block"] := ["Custom", "Polybius columnar — CIPHER", "Polybius columnar — ZEBRAS", "Polybius columnar — random key"]
    m["Base16 separated per letter"] := ["Custom", "Base16 separated per letter"]
    m["Base32Hex per letter"] := ["Custom", "Base32Hex per letter"]
    m["Base64URL per letter"] := ["Custom", "Base64URL per letter"]
    m["Base91 per letter"] := ["Custom", "Base91 per letter"]
    m["RFC1924 Base85 per letter"] := ["Custom", "RFC1924 Base85 per letter"]
    m["yEnc per letter"] := ["Custom", "yEnc per letter"]
    m["PEM armor token"] := ["Custom", "PEM armor token"]
    m["MessagePack hex token"] := ["Custom", "MessagePack hex token"]
    m["Intel HEX record"] := ["Custom", "Intel HEX record"]
    m["Motorola S-record"] := ["Custom", "Motorola S-record"]
    m["Cistercian numerals"] := ["Custom", "Cistercian numerals"]
    m["Murray code"] := ["Custom", "Murray code"]
    m["APCO phonetic words"] := ["Custom", "APCO phonetic words"]
    m["International signal phrases"] := ["Custom", "International signal phrases"]
    m["Younger Futhark runes"] := ["Custom", "Younger Futhark runes"]
    m["Cirth runes"] := ["Custom", "Cirth runes"]
    m["Tengwar tokens"] := ["Custom", "Tengwar tokens"]
    m["Zodiac symbols"] := ["Custom", "Zodiac symbols"]
    m["Wingdings tokens"] := ["Custom", "Wingdings tokens"]
    m["Braille grade 1"] := ["Custom", "Braille grade 1"]
    m["Bacon biliteral custom"] := ["Custom", "Bacon biliteral — AB", "Bacon biliteral — 01", "Bacon biliteral — dot dash"]
    m["Solresol syllables"] := ["Custom", "Solresol syllables"]
    m["Music notes"] := ["Custom", "Music notes"]
    m["Null acrostic words"] := ["Custom", "Null acrostic words"]
    m["Acrostic cover words"] := ["Custom", "Acrostic cover — COVER", "Acrostic cover — random tail"]
    m["Calculator spelling"] := ["Custom", "Calculator spelling"]
    m["Vanity phone digits"] := ["Custom", "Vanity phone digits"]
    m["Keyboard coordinates"] := ["Custom", "Keyboard coordinates"]
    m["QWERTY adjacent up"] := ["Custom", "QWERTY adjacent up"]
    m["QWERTY adjacent down"] := ["Custom", "QWERTY adjacent down"]
    m["Chessboard coordinates"] := ["Custom", "Chessboard coordinates"]
    m["Word Caesar"] := ["Custom", "Word Caesar"]
    m["Backslang reverse"] := ["Custom", "Backslang reverse"]
    m["Pig Latin"] := ["Custom", "Pig Latin"]
    m["Rovarspraket"] := ["Custom", "Rovarspraket"]
    m["Tutnese token"] := ["Custom", "Tutnese token"]
    m["Base3 per letter"] := ["Custom", "Base3 per letter"]
    m["Base4 per letter"] := ["Custom", "Base4 per letter"]
    m["Base8 per letter"] := ["Custom", "Base8 per letter"]
    m["Base9 per letter"] := ["Custom", "Base9 per letter"]
    m["Unary index"] := ["Custom", "Unary index"]
    m["Ternary index"] := ["Custom", "Ternary index"]
    m["Balanced ternary index"] := ["Custom", "Balanced ternary index"]
    m["Hex color code"] := ["Custom", "Hex color code"]
    m["CSS hex escape"] := ["Custom", "CSS hex escape"]
    m["JavaScript hex escape"] := ["Custom", "JavaScript hex escape"]
    m["C string escape"] := ["Custom", "C string escape"]
    m["JSON string escape"] := ["Custom", "JSON string escape"]
    m["Octal escape token"] := ["Custom", "Octal escape token"]
    m["Data URI token"] := ["Custom", "Data URI token"]
    m["URL form token"] := ["Custom", "URL form token"]
    m["Netstring token"] := ["Custom", "Netstring token"]
    m["Bencode string token"] := ["Custom", "Bencode string token"]
    m["XXEncode per letter"] := ["Custom", "XXEncode per letter"]
    m["Gray code 8-bit"] := ["Custom", "Gray code 8-bit"]
    m["Parity bit token"] := ["Custom", "Parity bit token"]
    m["Hamming 7,4 token"] := ["Custom", "Hamming 7,4 token"]
    m["Hamming 15,11 token"] := ["Custom", "Hamming 15,11 token"]
    m["LEB128 token"] := ["Custom", "LEB128 token"]
    m["Elias gamma token"] := ["Custom", "Elias gamma token"]
    m["Elias delta token"] := ["Custom", "Elias delta token"]
    m["Fibonacci universal token"] := ["Custom", "Fibonacci universal token"]
    m["Golomb Rice token"] := ["Custom", "Golomb Rice token"]
    m["Luhn check token"] := ["Custom", "Luhn check token"]
    m["Damm check token"] := ["Custom", "Damm check token"]
    m["CRC8 token"] := ["Custom", "CRC8 token"]
    m["CRC16 token"] := ["Custom", "CRC16 token"]
    m["CRC32 token"] := ["Custom", "CRC32 token"]
    m["Adler32 token"] := ["Custom", "Adler32 token"]
    m["Fletcher16 token"] := ["Custom", "Fletcher16 token"]
    m["RLE token"] := ["Custom", "RLE token"]
    m["Move-to-front index"] := ["Custom", "Move-to-front index"]
    m["Caesar box mini block"] := ["Custom", "Caesar box mini block"]
    m["Skip permutation block"] := ["Custom", "Skip permutation block"]
    m["Vertical transposition block"] := ["Custom", "Vertical transposition block"]
    m["Rail fence spaces block"] := ["Custom", "Rail fence spaces block"]
    m["DNA triplet code"] := ["Custom", "DNA triplet code"]
    m["RNA triplet code"] := ["Custom", "RNA triplet code"]
    m["Protein name code"] := ["Custom", "Protein name code"]
    m["Resistor color code"] := ["Custom", "Resistor color code"]
    m["Semaphore arms"] := ["Custom", "Semaphore arms"]
    m["Keyed Caesar"] := ["Custom", "Keyed Caesar — CIPHER +3", "Keyed Caesar — MONARCHY +5", "Keyed Caesar — random key"]
    m["Keyed progressive Caesar"] := ["Custom", "Keyed progressive — CIPHER", "Keyed progressive — MONARCHY", "Keyed progressive — random key"]
    m["Interrupted key Vigenere"] := ["Custom", "Interrupted key — CIPHER", "Interrupted key — SECRET", "Interrupted key — random key"]
    m["Progressive key Vigenere"] := ["Custom", "Progressive key — LEMON", "Progressive key — CIPHER", "Progressive key — random key"]
    m["Variant Beaufort Autokey"] := ["Custom", "Variant Beaufort autokey — FORT", "Variant Beaufort autokey — CIPHER", "Variant Beaufort autokey — random key"]
    m["Running key book"] := ["Custom", "Running book — THEQUICKBROWNFOX", "Running book — CRYPTOGRAPHY", "Running book — random long key"]
    m["Progressive Beaufort"] := ["Custom", "Progressive Beaufort — FORT", "Progressive Beaufort — CIPHER", "Progressive Beaufort — random key"]
    m["Progressive Variant Beaufort"] := ["Custom", "Progressive Variant Beaufort — FORT", "Progressive Variant Beaufort — CIPHER", "Progressive Variant Beaufort — random key"]
    m["Porta Autokey"] := ["Custom", "Porta autokey — PORTA", "Porta autokey — CIPHER", "Porta autokey — random key"]
    m["Triangular Caesar shift"] := ["Custom", "Triangular Caesar shift"]
    m["Lucas Caesar shift"] := ["Custom", "Lucas Caesar shift"]
    m["Square Caesar shift"] := ["Custom", "Square Caesar shift"]
    m["Cube Caesar shift"] := ["Custom", "Cube Caesar shift"]
    m["Digital root Caesar shift"] := ["Custom", "Digital root Caesar shift"]
    m["Alternating Atbash"] := ["Custom", "Alternating Atbash"]
    m["Vigenere Atbash hybrid"] := ["Custom", "Vigenere Atbash hybrid"]
    m["Polybius 0-based keyed"] := ["Custom", "Polybius 0 keyed — CIPHER", "Polybius 0 keyed — MONARCHY", "Polybius 0 keyed — random key"]
    m["Polybius letter coords keyed"] := ["Custom", "Polybius letters — CIPHER", "Polybius letters — MONARCHY", "Polybius letters — random key"]
    m["Grandpre coordinate"] := ["Custom", "Grandpre — CRYPTOGRAPHY", "Grandpre — MONARCHY", "Grandpre — random grid"]
    m["Fractionated Polybius token"] := ["Custom", "Fractionated Polybius — CIPHER", "Fractionated Polybius — MONARCHY", "Fractionated Polybius — random key"]
    m["Base26 A0Z25"] := ["Custom", "Base26 A0Z25"]
    m["ASCII hex lowercase"] := ["Custom", "ASCII hex lowercase"]
    m["ASCII decimal padded"] := ["Custom", "ASCII decimal padded"]
    m["Binary ASCII 7-bit"] := ["Custom", "Binary ASCII 7-bit"]
    m["Unicode decimal code point"] := ["Custom", "Unicode decimal code point"]
    m["UTF-16BE hex"] := ["Custom", "UTF-16BE hex"]
    m["UTF-32BE hex"] := ["Custom", "UTF-32BE hex"]
    m["UTF-32LE hex"] := ["Custom", "UTF-32LE hex"]
    m["XML decimal entity"] := ["Custom", "XML decimal entity"]
    m["XML hex entity"] := ["Custom", "XML hex entity"]
    m["Latin alphabet names"] := ["Custom", "Latin alphabet names"]
    m["Greek alphabet names"] := ["Custom", "Greek alphabet names"]
    m["Hebrew gematria"] := ["Custom", "Hebrew gematria"]
    m["Greek isopsephy"] := ["Custom", "Greek isopsephy"]
    m["Scrabble values"] := ["Custom", "Scrabble values"]
    m["Letter frequency rank"] := ["Custom", "Letter frequency rank"]
    m["Periodic atomic numbers"] := ["Custom", "Periodic atomic numbers"]
    m["Periodic element symbols"] := ["Custom", "Periodic element symbols"]
    m["NATO compact"] := ["Custom", "NATO compact"]
    m["LAPD phonetic words"] := ["Custom", "LAPD phonetic words"]
    m["RAF phonetic words"] := ["Custom", "RAF phonetic words"]
    m["Morse length code"] := ["Custom", "Morse length code"]
    m["Morse dash count"] := ["Custom", "Morse dash count"]
    m["Morse dot count"] := ["Custom", "Morse dot count"]
    m["Flag token alphabet"] := ["Custom", "Flag token alphabet"]
    m["Moon type tokens"] := ["Custom", "Moon type tokens"]
    m["Theban tokens"] := ["Custom", "Theban tokens"]
    m["Dancing Men tokens"] := ["Custom", "Dancing Men tokens"]
    m["Standard Galactic tokens"] := ["Custom", "Standard Galactic tokens"]
    m["Aurebesh tokens"] := ["Custom", "Aurebesh tokens"]
    m["Mathematical bold letters"] := ["Custom", "Mathematical bold letters"]
    m["Mathematical italic letters"] := ["Custom", "Mathematical italic letters"]
    m["Sans-serif letters"] := ["Custom", "Sans-serif letters"]
    m["Sans-serif bold letters"] := ["Custom", "Sans-serif bold letters"]
    m["Monospace letters"] := ["Custom", "Monospace letters"]
    m["Negative circled letters"] := ["Custom", "Negative circled letters"]
    m["Box drawing code"] := ["Custom", "Box drawing code"]
    m["Geometric shape alphabet"] := ["Custom", "Geometric shape alphabet"]
    m["Vigenere keyed alphabet"] := ["Custom", "Vigenere keyed alphabet"]
    m["Beaufort keyed alphabet"] := ["Custom", "Beaufort keyed alphabet"]
    m["Variant Beaufort keyed alphabet"] := ["Custom", "Variant Beaufort keyed alphabet"]
    m["Autokey keyed alphabet"] := ["Custom", "Autokey keyed alphabet"]
    m["Porta numeric table"] := ["Custom", "Porta numeric table"]
    m["Porta reverse table"] := ["Custom", "Porta reverse table"]
    m["Atbash then Vigenere"] := ["Custom", "Atbash then Vigenere"]
    m["Vigenere then Atbash"] := ["Custom", "Vigenere then Atbash"]
    m["Running Atbash key"] := ["Custom", "Running Atbash key"]
    m["Autokey Atbash"] := ["Custom", "Autokey Atbash"]
    m["Progressive Affine"] := ["Custom", "Progressive Affine"]
    m["Progressive Decimation"] := ["Custom", "Progressive Decimation"]
    m["Multiplicative cipher x3"] := ["Custom", "Multiplicative cipher x3"]
    m["Multiplicative cipher x5"] := ["Custom", "Multiplicative cipher x5"]
    m["Multiplicative cipher x7"] := ["Custom", "Multiplicative cipher x7"]
    m["Multiplicative cipher x11"] := ["Custom", "Multiplicative cipher x11"]
    m["Multiplicative cipher x17"] := ["Custom", "Multiplicative cipher x17"]
    m["Multiplicative cipher x25"] := ["Custom", "Multiplicative cipher x25"]
    m["Baconian binary"] := ["Custom", "Baconian binary"]
    m["Baconian reversed"] := ["Custom", "Baconian reversed"]
    m["Baconian dots dashes"] := ["Custom", "Baconian dots dashes"]
    m["Baconian visible whitespace"] := ["Custom", "Baconian visible whitespace"]
    m["Morse binary 10"] := ["Custom", "Morse binary 10"]
    m["Morse binary 01"] := ["Custom", "Morse binary 01"]
    m["Morse with slash"] := ["Custom", "Morse with slash"]
    m["Morse compact digits"] := ["Custom", "Morse compact digits"]
    m["Morse decimal token"] := ["Custom", "Morse decimal token"]
    m["Morse hex token"] := ["Custom", "Morse hex token"]
    m["Polybius 6x6"] := ["Custom", "Polybius 6x6"]
    m["ADFGVX 6x6 coords"] := ["Custom", "ADFGVX 6x6 coords"]
    m["Bifid numeric fraction"] := ["Custom", "Bifid numeric fraction"]
    m["Trifid numeric fraction"] := ["Custom", "Trifid numeric fraction"]
    m["Nihilist plain coordinate"] := ["Custom", "Nihilist plain coordinate"]
    m["Checkerboard 6x6 coords"] := ["Custom", "Checkerboard 6x6 coords"]
    m["Base5 index"] := ["Custom", "Base5 index"]
    m["Base6 index"] := ["Custom", "Base6 index"]
    m["Base7 index"] := ["Custom", "Base7 index"]
    m["Base11 index"] := ["Custom", "Base11 index"]
    m["Base12 index"] := ["Custom", "Base12 index"]
    m["Base16 index"] := ["Custom", "Base16 index"]
    m["Base20 index"] := ["Custom", "Base20 index"]
    m["QR alphanumeric index"] := ["Custom", "QR alphanumeric index"]
    m["Code39 token"] := ["Custom", "Code39 token"]
    m["Codabar token"] := ["Custom", "Codabar token"]
    m["Code128 token"] := ["Custom", "Code128 token"]
    m["ITF token"] := ["Custom", "ITF token"]
    m["UPC-A check token"] := ["Custom", "UPC-A check token"]
    m["EAN-13 check token"] := ["Custom", "EAN-13 check token"]
    m["ISBN-10 check token"] := ["Custom", "ISBN-10 check token"]
    m["ISBN-13 check token"] := ["Custom", "ISBN-13 check token"]
    m["Mathematical double-struck"] := ["Custom", "Mathematical double-struck"]
    m["Mathematical bold italic"] := ["Custom", "Mathematical bold italic"]
    m["Bold script letters"] := ["Custom", "Bold script letters"]
    m["Bold fraktur letters"] := ["Custom", "Bold fraktur letters"]
    m["Sans-serif italic letters"] := ["Custom", "Sans-serif italic letters"]
    m["Sans-serif bold italic letters"] := ["Custom", "Sans-serif bold italic letters"]
    m["Greek actual letters"] := ["Custom", "Greek actual letters"]
    m["Hebrew actual letters"] := ["Custom", "Hebrew actual letters"]
    m["Cyrillic actual letters"] := ["Custom", "Cyrillic actual letters"]
    m["Armenian actual letters"] := ["Custom", "Armenian actual letters"]
    m["Georgian actual letters"] := ["Custom", "Georgian actual letters"]
    m["Katakana phonetic"] := ["Custom", "Katakana phonetic"]
    m["Latin reverse custom"] := ["Custom", "Latin reverse custom"]
    m["Headline puzzle words"] := ["Custom", "Headline puzzle words"]
    m["Dictionary code index"] := ["Custom", "Dictionary code index"]
    m["Raster bits token"] := ["Custom", "Raster bits token"]
    m["Whitespace binary token"] := ["Custom", "Whitespace binary token"]
    m["Snow stego spaces token"] := ["Custom", "Snow stego spaces token"]
    m["OpenPGP armor token"] := ["Custom", "OpenPGP armor token"]
    m["Base100 emoji byte"] := ["Custom", "Base100 emoji byte"]
    m["Hexdump byte"] := ["Custom", "Hexdump byte"]
    m["Binary endian word"] := ["Custom", "Binary endian word"]
    m["CRC64 token"] := ["Custom", "CRC64 token"]
    m["Fletcher32 token"] := ["Custom", "Fletcher32 token"]
    m["Verhoeff check token"] := ["Custom", "Verhoeff check token"]
    m["MD5 toy token"] := ["Custom", "MD5 toy token"]
    m["SHA1 toy token"] := ["Custom", "SHA1 toy token"]
    m["SHA256 toy token"] := ["Custom", "SHA256 toy token"]
    m["CRC16 CCITT token"] := ["Custom", "CRC16 CCITT token"]
    m["Punycode ascii token"] := ["Custom", "Punycode ascii token"]
    m["Zero width binary visible"] := ["Custom", "Zero width binary visible"]
    m["Invisible unicode visible"] := ["Custom", "Invisible unicode visible"]
    m["ROT18 alpha"] := ["Custom", "ROT18 alpha"]
    m["Knock code"] := ["Custom", "Knock code"]
    m["Morse fractionated ADFGX"] := ["Custom", "Morse fractionated ADFGX"]
    m["Morse syllable token"] := ["Custom", "Morse syllable token"]
    m["Gold-Bug cipher symbols"] := ["Custom", "Gold-Bug cipher symbols"]
    m["Rosicrucian cipher symbols"] := ["Custom", "Rosicrucian cipher symbols"]
    m["Templar cipher symbols"] := ["Custom", "Templar cipher symbols"]
    m["Malachim alphabet tokens"] := ["Custom", "Malachim alphabet tokens"]
    m["Celestial alphabet tokens"] := ["Custom", "Celestial alphabet tokens"]
    m["Enochian alphabet tokens"] := ["Custom", "Enochian alphabet tokens"]
    m["Phoenician letters"] := ["Custom", "Phoenician letters"]
    m["Ugaritic cuneiform"] := ["Custom", "Ugaritic cuneiform"]
    m["Etruscan tokens"] := ["Custom", "Etruscan tokens"]
    m["Gothic letters"] := ["Custom", "Gothic letters"]
    m["Coptic letters"] := ["Custom", "Coptic letters"]
    m["Anglo-Saxon runes"] := ["Custom", "Anglo-Saxon runes"]
    m["Baudot tape holes"] := ["Custom", "Baudot tape holes"]
    m["Murray punched tape"] := ["Custom", "Murray punched tape"]
    m["Hollerith punch code"] := ["Custom", "Hollerith punch code"]
    m["EBCDIC decimal"] := ["Custom", "EBCDIC decimal"]
    m["IBM card row punch"] := ["Custom", "IBM card row punch"]
    m["Baconian slash"] := ["Custom", "Baconian slash"]
    m["Baconian high-low"] := ["Custom", "Baconian high-low"]
    m["Polybius checker A-E"] := ["Custom", "Polybius checker A-E"]
    m["Polybius checker 0-4"] := ["Custom", "Polybius checker 0-4"]
    m["Tap code knocks"] := ["Custom", "Tap code knocks"]
    m["Prison tap code"] := ["Custom", "Prison tap code"]
    m["Fractionated tap code"] := ["Custom", "Fractionated tap code"]
    m["Bifid coordinate stream"] := ["Custom", "Bifid coordinate stream"]
    m["Trifid coordinate stream"] := ["Custom", "Trifid coordinate stream"]
    m["Nihilist plus key stream"] := ["Custom", "Nihilist plus key stream"]
    m["Hill coordinate token"] := ["Custom", "Hill coordinate token"]
    m["Modular inverse index"] := ["Custom", "Modular inverse index"]
    m["Affine family token"] := ["Custom", "Affine family token"]
    m["OTP numeric token"] := ["Custom", "OTP numeric token"]
    m["Vernam bitmask token"] := ["Custom", "Vernam bitmask token"]
    m["RC4 keystream token"] := ["Custom", "RC4 keystream token"]
    m["ChaCha toy token"] := ["Custom", "ChaCha toy token"]
    m["Salsa toy token"] := ["Custom", "Salsa toy token"]
    m["Z85 index"] := ["Custom", "Z85 index"]
    m["Bech32 index"] := ["Custom", "Bech32 index"]
    m["z-base-32 index"] := ["Custom", "z-base-32 index"]
    m["Crockford byte token"] := ["Custom", "Crockford byte token"]
    m["Caesar reverse alphabet shift"] := ["Custom", "Caesar reverse alphabet shift"]
    m["Atbash Caesar shift"] := ["Custom", "Atbash Caesar shift"]
    m["ROT13 then Atbash"] := ["Custom", "ROT13 then Atbash"]
    m["Vigenere reversed alphabet"] := ["Custom", "Vigenere reversed alphabet"]
    m["Beaufort reversed alphabet"] := ["Custom", "Beaufort reversed alphabet"]
    m["Gronsfeld reversed alphabet"] := ["Custom", "Gronsfeld reversed alphabet"]
    m["Autokey reversed alphabet"] := ["Custom", "Autokey reversed alphabet"]
    m["Progressive key Beaufort"] := ["Custom", "Progressive key Beaufort"]
    m["Interrupted Beaufort"] := ["Custom", "Interrupted Beaufort"]
    m["Keyed Beaufort"] := ["Custom", "Keyed Beaufort"]
    m["Keyed Variant Beaufort"] := ["Custom", "Keyed Variant Beaufort"]
    m["Slide Vigenere"] := ["Custom", "Slide Vigenere"]
    m["Diana reciprocal"] := ["Custom", "Diana reciprocal"]
    m["Vigenere Fibonacci stream"] := ["Custom", "Vigenere Fibonacci stream"]
    m["Vigenere Lucas stream"] := ["Custom", "Vigenere Lucas stream"]
    m["Vigenere prime stream"] := ["Custom", "Vigenere prime stream"]
    m["Vigenere triangular stream"] := ["Custom", "Vigenere triangular stream"]
    m["Multiplicative progressive"] := ["Custom", "Multiplicative progressive"]
    m["Affine with key shift"] := ["Custom", "Affine with key shift"]
    m["Caesar keyed stream"] := ["Custom", "Caesar keyed stream"]
    m["Porta progressive reverse"] := ["Custom", "Porta progressive reverse"]
    m["Trithemius descending"] := ["Custom", "Trithemius descending"]
    m["Polybius row letters"] := ["Custom", "Polybius row letters"]
    m["Polybius column letters"] := ["Custom", "Polybius column letters"]
    m["Polybius chess coords"] := ["Custom", "Polybius chess coords"]
    m["Polybius barcode token"] := ["Custom", "Polybius barcode token"]
    m["Polybius binary coords"] := ["Custom", "Polybius binary coords"]
    m["Bifid raw coords"] := ["Custom", "Bifid raw coords"]
    m["Trifid raw coords"] := ["Custom", "Trifid raw coords"]
    m["ADFGX spaced"] := ["Custom", "ADFGX spaced"]
    m["ADFGVX spaced"] := ["Custom", "ADFGVX spaced"]
    m["Nihilist keyed number"] := ["Custom", "Nihilist keyed number"]
    m["Checkerboard serial"] := ["Custom", "Checkerboard serial"]
    m["Tap binary token"] := ["Custom", "Tap binary token"]
    m["Knock binary token"] := ["Custom", "Knock binary token"]
    m["Baconian 12345"] := ["Custom", "Baconian 12345"]
    m["Baconian emoji"] := ["Custom", "Baconian emoji"]
    m["Baconian morse"] := ["Custom", "Baconian morse"]
    m["Baconian Roman"] := ["Custom", "Baconian Roman"]
    m["LCG stream hex"] := ["Custom", "LCG stream hex"]
    m["Xorshift stream hex"] := ["Custom", "Xorshift stream hex"]
    m["Blum Blum Shub toy"] := ["Custom", "Blum Blum Shub toy"]
    m["Fibonacci LFSR toy"] := ["Custom", "Fibonacci LFSR toy"]
    m["Vernam decimal byte"] := ["Custom", "Vernam decimal byte"]
    m["OTP base26 token"] := ["Custom", "OTP base26 token"]
    m["Running key numeric"] := ["Custom", "Running key numeric"]
    m["Base24 index"] := ["Custom", "Base24 index"]
    m["Base30 index"] := ["Custom", "Base30 index"]
    m["Base64 index"] := ["Custom", "Base64 index"]
    m["Base85 index"] := ["Custom", "Base85 index"]
    m["ASCII base3 byte"] := ["Custom", "ASCII base3 byte"]
    m["ASCII base4 byte"] := ["Custom", "ASCII base4 byte"]
    m["ASCII base5 byte"] := ["Custom", "ASCII base5 byte"]
    m["ASCII base6 byte"] := ["Custom", "ASCII base6 byte"]
    m["ASCII base12 byte"] := ["Custom", "ASCII base12 byte"]
    m["ASCII base36 byte"] := ["Custom", "ASCII base36 byte"]
    m["UTF-8 bytes decimal"] := ["Custom", "UTF-8 bytes decimal"]
    m["UTF-8 bytes hex spaced"] := ["Custom", "UTF-8 bytes hex spaced"]
    m["Java unicode escape"] := ["Custom", "Java unicode escape"]
    m["Python unicode escape"] := ["Custom", "Python unicode escape"]
    m["CSharp unicode escape"] := ["Custom", "CSharp unicode escape"]
    m["CSS unicode padded"] := ["Custom", "CSS unicode padded"]
    m["SQL CHAR token"] := ["Custom", "SQL CHAR token"]
    m["PowerShell char token"] := ["Custom", "PowerShell char token"]
    m["Decimal entity padded"] := ["Custom", "Decimal entity padded"]
    m["Hex entity padded"] := ["Custom", "Hex entity padded"]
    m["Percent lowercase"] := ["Custom", "Percent lowercase"]
    m["Percent uppercase spaced"] := ["Custom", "Percent uppercase spaced"]
    m["Quoted printable soft token"] := ["Custom", "Quoted printable soft token"]
    m["Morse prosign token"] := ["Custom", "Morse prosign token"]
    m["NATO initials only"] := ["Custom", "NATO initials only"]
    m["Pigpen grid code"] := ["Custom", "Pigpen grid code"]
    m["Templar cross code"] := ["Custom", "Templar cross code"]
    m["Semaphore compass"] := ["Custom", "Semaphore compass"]
    m["Braille dots token"] := ["Custom", "Braille dots token"]
    m["Moon phase alphabet"] := ["Custom", "Moon phase alphabet"]
    m["Planet sequence alphabet"] := ["Custom", "Planet sequence alphabet"]
    m["Diceware coordinate token"] := ["Custom", "Diceware coordinate token"]
    m["Reciprocal Vigenere"] := ["Custom", "Reciprocal Vigenere"]
    m["Reciprocal Gronsfeld"] := ["Custom", "Reciprocal Gronsfeld"]
    m["Beaufort Fibonacci stream"] := ["Custom", "Beaufort Fibonacci stream"]
    m["Beaufort prime stream"] := ["Custom", "Beaufort prime stream"]
    m["Variant Beaufort Fibonacci"] := ["Custom", "Variant Beaufort Fibonacci"]
    m["Variant Beaufort prime"] := ["Custom", "Variant Beaufort prime"]
    m["Autokey Caesar stream"] := ["Custom", "Autokey Caesar stream"]
    m["Progressive Atbash stream"] := ["Custom", "Progressive Atbash stream"]
    m["Keyed Polybius 0-4"] := ["Custom", "Keyed Polybius 0-4"]
    m["Keyed Polybius A-E"] := ["Custom", "Keyed Polybius A-E"]
    m["Keyed Tap coordinate"] := ["Custom", "Keyed Tap coordinate"]
    m["ADFGX numeric labels"] := ["Custom", "ADFGX numeric labels"]
    m["ADFGVX numeric labels"] := ["Custom", "ADFGVX numeric labels"]
    m["Polybius mixed 6x6 keyed"] := ["Custom", "Polybius mixed 6x6 keyed"]
    m["Checkerboard 10x10 token"] := ["Custom", "Checkerboard 10x10 token"]
    m["VIC chain addition toy"] := ["Custom", "VIC chain addition toy"]
    m["Nihilist zero padded"] := ["Custom", "Nihilist zero padded"]
    m["Nihilist keyed hex"] := ["Custom", "Nihilist keyed hex"]
    m["Bifid split token"] := ["Custom", "Bifid split token"]
    m["Trifid layer token"] := ["Custom", "Trifid layer token"]
    m["Playfair digraph marker"] := ["Custom", "Playfair digraph marker"]
    m["Hill mod26 vector token"] := ["Custom", "Hill mod26 vector token"]
    m["Modular square index"] := ["Custom", "Modular square index"]
    m["Modular cube index"] := ["Custom", "Modular cube index"]
    m["Power residue index"] := ["Custom", "Power residue index"]
    m["Quadratic residue token"] := ["Custom", "Quadratic residue token"]
    m["QR format bits token"] := ["Custom", "QR format bits token"]
    m["Aztec barcode token"] := ["Custom", "Aztec barcode token"]
    m["PDF417 codeword token"] := ["Custom", "PDF417 codeword token"]
    m["DataMatrix codeword token"] := ["Custom", "DataMatrix codeword token"]
    m["Code93 token"] := ["Custom", "Code93 token"]
    m["MSI check token"] := ["Custom", "MSI check token"]
    m["Interleaved 2 of 5 pair"] := ["Custom", "Interleaved 2 of 5 pair"]
    m["POSTNET digit token"] := ["Custom", "POSTNET digit token"]
    m["PLANET digit token"] := ["Custom", "PLANET digit token"]
    m["Royal Mail 4-state token"] := ["Custom", "Royal Mail 4-state token"]
    m["KIX 4-state token"] := ["Custom", "KIX 4-state token"]
    m["Facing identification mark"] := ["Custom", "Facing identification mark"]
    m["OCR-A token"] := ["Custom", "OCR-A token"]
    m["MICR E13B token"] := ["Custom", "MICR E13B token"]
    m["MIME quoted word Q"] := ["Custom", "MIME quoted word Q"]
    m["MIME quoted word B"] := ["Custom", "MIME quoted word B"]
    m["LDAP hex escape"] := ["Custom", "LDAP hex escape"]
    m["Regex unicode escape"] := ["Custom", "Regex unicode escape"]
    m["XML CDATA token"] := ["Custom", "XML CDATA token"]
    m["CSV quoted token"] := ["Custom", "CSV quoted token"]
    m["Shell ANSI C escape"] := ["Custom", "Shell ANSI C escape"]
    m["Bash hex token"] := ["Custom", "Bash hex token"]
    m["Python bytes token"] := ["Custom", "Python bytes token"]
    m["Ruby hex token"] := ["Custom", "Ruby hex token"]
    m["Perl hex token"] := ["Custom", "Perl hex token"]
    m["Go rune token"] := ["Custom", "Go rune token"]
    m["Rust unicode token"] := ["Custom", "Rust unicode token"]
    m["HTML named fallback"] := ["Custom", "HTML named fallback"]
    m["SGML entity token"] := ["Custom", "SGML entity token"]
    m["TeX char token"] := ["Custom", "TeX char token"]
    m["PostScript char token"] := ["Custom", "PostScript char token"]
    m["Assembly DB hex"] := ["Custom", "Assembly DB hex"]
    m["Intel asm char"] := ["Custom", "Intel asm char"]
    m["MIPS ascii byte"] := ["Custom", "MIPS ascii byte"]
    m["Byte pair hex token"] := ["Custom", "Byte pair hex token"]
    m["Nibble swap hex"] := ["Custom", "Nibble swap hex"]
    m["Bit reverse byte"] := ["Custom", "Bit reverse byte"]
    m["Gray code reflected"] := ["Custom", "Gray code reflected"]
    m["Excess-3 BCD token"] := ["Custom", "Excess-3 BCD token"]
    m["BCD 2421 token"] := ["Custom", "BCD 2421 token"]
    m["BCD 5211 token"] := ["Custom", "BCD 5211 token"]
    m["Johnson code token"] := ["Custom", "Johnson code token"]
    m["One-hot index token"] := ["Custom", "One-hot index token"]
    m["Two-hot index token"] := ["Custom", "Two-hot index token"]
    m["Huffman toy token"] := ["Custom", "Huffman toy token"]
    m["Shannon-Fano toy token"] := ["Custom", "Shannon-Fano toy token"]
    m["Morse American token"] := ["Custom", "Morse American token"]
    m["Chappe semaphore token"] := ["Custom", "Chappe semaphore token"]
    m["Optical telegraph token"] := ["Custom", "Optical telegraph token"]
    m["Navajo code talker token"] := ["Custom", "Navajo code talker token"]
    m["Commercial code word"] := ["Custom", "Commercial code word"]
    m["Telegraph code word"] := ["Custom", "Telegraph code word"]
    m["Postal abbreviation token"] := ["Custom", "Postal abbreviation token"]
    m["Weather code token"] := ["Custom", "Weather code token"]
    m["Vigenere minus key"] := ["Custom", "Vigenere minus key"]
    m["Vigenere plus Atbash"] := ["Custom", "Vigenere plus Atbash"]
    m["Beaufort Atbash hybrid"] := ["Custom", "Beaufort Atbash hybrid"]
    m["Variant Beaufort Atbash hybrid"] := ["Custom", "Variant Beaufort Atbash hybrid"]
    m["Caesar sine wave shift"] := ["Custom", "Caesar sine wave shift"]
    m["Caesar cosine wave shift"] := ["Custom", "Caesar cosine wave shift"]
    m["Caesar sawtooth shift"] := ["Custom", "Caesar sawtooth shift"]
    m["Caesar square wave shift"] := ["Custom", "Caesar square wave shift"]
    m["Caesar triangular wave shift"] := ["Custom", "Caesar triangular wave shift"]
    m["Prime gap Caesar shift"] := ["Custom", "Prime gap Caesar shift"]
    m["Pell Caesar shift"] := ["Custom", "Pell Caesar shift"]
    m["Jacobsthal Caesar shift"] := ["Custom", "Jacobsthal Caesar shift"]
    m["Padovan Caesar shift"] := ["Custom", "Padovan Caesar shift"]
    m["Tetranacci Caesar shift"] := ["Custom", "Tetranacci Caesar shift"]
    m["Keyed reciprocal substitution"] := ["Custom", "Keyed reciprocal substitution"]
    m["Keyed reverse substitution"] := ["Custom", "Keyed reverse substitution"]
    m["Keyword transposed alphabet"] := ["Custom", "Keyword transposed alphabet"]
    m["Alphabet rail split"] := ["Custom", "Alphabet rail split"]
    m["Alphabet odd-even split"] := ["Custom", "Alphabet odd-even split"]
    m["Alphabet vowel-first"] := ["Custom", "Alphabet vowel-first"]
    m["Alphabet consonant-first"] := ["Custom", "Alphabet consonant-first"]
    m["Alphabet frequency order"] := ["Custom", "Alphabet frequency order"]
    m["Polybius Greek labels"] := ["Custom", "Polybius Greek labels"]
    m["Polybius Morse labels"] := ["Custom", "Polybius Morse labels"]
    m["Polybius Roman labels"] := ["Custom", "Polybius Roman labels"]
    m["Polybius symbol coords"] := ["Custom", "Polybius symbol coords"]
    m["Polybius NATO coords"] := ["Custom", "Polybius NATO coords"]
    m["Checkerboard phone coords"] := ["Custom", "Checkerboard phone coords"]
    m["Checkerboard keyboard coords"] := ["Custom", "Checkerboard keyboard coords"]
    m["Checkerboard hex coords"] := ["Custom", "Checkerboard hex coords"]
    m["ADFGX reversed square"] := ["Custom", "ADFGX reversed square"]
    m["ADFGVX reversed square"] := ["Custom", "ADFGVX reversed square"]
    m["Baconian Greek"] := ["Custom", "Baconian Greek"]
    m["Baconian binary spaced"] := ["Custom", "Baconian binary spaced"]
    m["Baconian quinary digits"] := ["Custom", "Baconian quinary digits"]
    m["Baconian 0-1 compact"] := ["Custom", "Baconian 0-1 compact"]
    m["Baconian braille"] := ["Custom", "Baconian braille"]
    m["Baconian flag token"] := ["Custom", "Baconian flag token"]
    m["Morse Unicode symbols"] := ["Custom", "Morse Unicode symbols"]
    m["Morse blocks"] := ["Custom", "Morse blocks"]
    m["Morse arrows"] := ["Custom", "Morse arrows"]
    m["Morse vowels consonants"] := ["Custom", "Morse vowels consonants"]
    m["Morse word code"] := ["Custom", "Morse word code"]
    m["Morse phone taps"] := ["Custom", "Morse phone taps"]
    m["Morse base3 token"] := ["Custom", "Morse base3 token"]
    m["Morse length-dash-dot"] := ["Custom", "Morse length-dash-dot"]
    m["ASCII base13 byte"] := ["Custom", "ASCII base13 byte"]
    m["ASCII base17 byte"] := ["Custom", "ASCII base17 byte"]
    m["ASCII base19 byte"] := ["Custom", "ASCII base19 byte"]
    m["ASCII base21 byte"] := ["Custom", "ASCII base21 byte"]
    m["ASCII base23 byte"] := ["Custom", "ASCII base23 byte"]
    m["ASCII base27 byte"] := ["Custom", "ASCII base27 byte"]
    m["ASCII base31 byte"] := ["Custom", "ASCII base31 byte"]
    m["ASCII base52 byte"] := ["Custom", "ASCII base52 byte"]
    m["UTF-8 binary compact"] := ["Custom", "UTF-8 binary compact"]
    m["UTF-8 hex colon"] := ["Custom", "UTF-8 hex colon"]
    m["UTF-16BE decimal"] := ["Custom", "UTF-16BE decimal"]
    m["UTF-32LE decimal"] := ["Custom", "UTF-32LE decimal"]
    m["URI component token"] := ["Custom", "URI component token"]
    m["CSS escape short"] := ["Custom", "CSS escape short"]
    m["HTML entity hex padded"] := ["Custom", "HTML entity hex padded"]
    m["XML entity decimal padded"] := ["Custom", "XML entity decimal padded"]
    m["Base64 no padding per letter"] := ["Custom", "Base64 no padding per letter"]
    m["Base32 no padding per letter"] := ["Custom", "Base32 no padding per letter"]
    m["Base85 ascii85 framed"] := ["Custom", "Base85 ascii85 framed"]
    m["Base91 index token"] := ["Custom", "Base91 index token"]
    m["CRC4 token"] := ["Custom", "CRC4 token"]
    m["CRC5 USB token"] := ["Custom", "CRC5 USB token"]
    m["CRC6 token"] := ["Custom", "CRC6 token"]
    m["CRC7 token"] := ["Custom", "CRC7 token"]
    m["CRC12 token"] := ["Custom", "CRC12 token"]
    m["CRC24 toy token"] := ["Custom", "CRC24 toy token"]
    m["LRC token"] := ["Custom", "LRC token"]
    m["XOR checksum token"] := ["Custom", "XOR checksum token"]
    m["EAN-8 check token"] := ["Custom", "EAN-8 check token"]
    m["Code11 check token"] := ["Custom", "Code11 check token"]
    m["Pharmacode token"] := ["Custom", "Pharmacode token"]
    m["Telepen token"] := ["Custom", "Telepen token"]
    m["Maxicode word token"] := ["Custom", "Maxicode word token"]
    m["QR byte mode token"] := ["Custom", "QR byte mode token"]
    m["DataMatrix ASCII token"] := ["Custom", "DataMatrix ASCII token"]
    m["Aztec compact word token"] := ["Custom", "Aztec compact word token"]
    m["RTTY mark-space token"] := ["Custom", "RTTY mark-space token"]
    m["Baudot reversed bits"] := ["Custom", "Baudot reversed bits"]
    m["ITA2 letters only token"] := ["Custom", "ITA2 letters only token"]
    m["Varicode token"] := ["Custom", "Varicode token"]
    m["Hellschreiber token"] := ["Custom", "Hellschreiber token"]
    m["AX25 callsign token"] := ["Custom", "AX25 callsign token"]
    m["AIS six-bit token"] := ["Custom", "AIS six-bit token"]
    m["Murray reversed bits"] := ["Custom", "Murray reversed bits"]
    m["Glagolitic letters"] := ["Custom", "Glagolitic letters"]
    m["Old Turkic runes"] := ["Custom", "Old Turkic runes"]
    m["Avestan letters"] := ["Custom", "Avestan letters"]
    m["Linear B tokens"] := ["Custom", "Linear B tokens"]
    m["Egyptian alphabet tokens"] := ["Custom", "Egyptian alphabet tokens"]
    m["Mayan bar-dot token"] := ["Custom", "Mayan bar-dot token"]
    m["Kaktovik numeral token"] := ["Custom", "Kaktovik numeral token"]
    m["Greek acrophonic token"] := ["Custom", "Greek acrophonic token"]
    m["Factoradic index"] := ["Custom", "Factoradic index"]
    m["Cantor pairing token"] := ["Custom", "Cantor pairing token"]
    m["Godel prime token"] := ["Custom", "Godel prime token"]
    m["Lehmer code token"] := ["Custom", "Lehmer code token"]
    m["Catalan number token"] := ["Custom", "Catalan number token"]
    m["Bell number token"] := ["Custom", "Bell number token"]
    m["Happy number token"] := ["Custom", "Happy number token"]
    m["Perfect square marker"] := ["Custom", "Perfect square marker"]
    m["Caesar Catalan shift"] := ["Custom", "Caesar Catalan shift"]
    m["Caesar Bell shift"] := ["Custom", "Caesar Bell shift"]
    m["Caesar Perrin shift"] := ["Custom", "Caesar Perrin shift"]
    m["Caesar Motzkin shift"] := ["Custom", "Caesar Motzkin shift"]
    m["Caesar Collatz shift"] := ["Custom", "Caesar Collatz shift"]
    m["Vigenere square stream"] := ["Custom", "Vigenere square stream"]
    m["Vigenere cube stream"] := ["Custom", "Vigenere cube stream"]
    m["Vigenere Catalan stream"] := ["Custom", "Vigenere Catalan stream"]
    m["Vigenere prime-gap stream"] := ["Custom", "Vigenere prime-gap stream"]
    m["Beaufort triangular stream"] := ["Custom", "Beaufort triangular stream"]
    m["Beaufort square stream"] := ["Custom", "Beaufort square stream"]
    m["Variant Beaufort Lucas stream"] := ["Custom", "Variant Beaufort Lucas stream"]
    m["Autokey Gronsfeld"] := ["Custom", "Autokey Gronsfeld"]
    m["Running key Beaufort"] := ["Custom", "Running key Beaufort"]
    m["Progressive ROT47 printable"] := ["Custom", "Progressive ROT47 printable"]
    m["Printable ASCII Caesar"] := ["Custom", "Printable ASCII Caesar"]
    m["Printable ASCII Atbash"] := ["Custom", "Printable ASCII Atbash"]
    m["Printable Vigenere"] := ["Custom", "Printable Vigenere"]
    m["Printable Beaufort"] := ["Custom", "Printable Beaufort"]
    m["Keyed alphabet reciprocal"] := ["Custom", "Keyed alphabet reciprocal"]
    m["Mixed alphabet ROT13"] := ["Custom", "Mixed alphabet ROT13"]
    m["Frequency keyed substitution"] := ["Custom", "Frequency keyed substitution"]
    m["Dvorak to QWERTY"] := ["Custom", "Dvorak to QWERTY"]
    m["AZERTY to QWERTY"] := ["Custom", "AZERTY to QWERTY"]
    m["Colemak to QWERTY"] := ["Custom", "Colemak to QWERTY"]
    m["QWERTY row rotate"] := ["Custom", "QWERTY row rotate"]
    m["Keyboard column code"] := ["Custom", "Keyboard column code"]
    m["Keyboard diagonal code"] := ["Custom", "Keyboard diagonal code"]
    m["Morse star bar"] := ["Custom", "Morse star bar"]
    m["Morse bullet dash"] := ["Custom", "Morse bullet dash"]
    m["Morse pulse widths"] := ["Custom", "Morse pulse widths"]
    m["Morse timed token"] := ["Custom", "Morse timed token"]
    m["Morse Japanese Wabun token"] := ["Custom", "Morse Japanese Wabun token"]
    m["Baconian lowercase uppercase"] := ["Custom", "Baconian lowercase uppercase"]
    m["Baconian chess pieces"] := ["Custom", "Baconian chess pieces"]
    m["Baconian dice faces"] := ["Custom", "Baconian dice faces"]
    m["Baconian roman binary"] := ["Custom", "Baconian roman binary"]
    m["Baconian hexadecimal"] := ["Custom", "Baconian hexadecimal"]
    m["Polybius 7x4"] := ["Custom", "Polybius 7x4"]
    m["Polybius 4x7"] := ["Custom", "Polybius 4x7"]
    m["Polybius 13x2"] := ["Custom", "Polybius 13x2"]
    m["Polybius zodiac labels"] := ["Custom", "Polybius zodiac labels"]
    m["Polybius planet labels"] := ["Custom", "Polybius planet labels"]
    m["ADFGX Morse square"] := ["Custom", "ADFGX Morse square"]
    m["ADFGVX phone square"] := ["Custom", "ADFGVX phone square"]
    m["Tap code 0-based"] := ["Custom", "Tap code 0-based"]
    m["Tap code row-column words"] := ["Custom", "Tap code row-column words"]
    m["Nihilist product token"] := ["Custom", "Nihilist product token"]
    m["Hill 2x2 coordinate token"] := ["Custom", "Hill 2x2 coordinate token"]
    m["Hill 3x3 coordinate token"] := ["Custom", "Hill 3x3 coordinate token"]
    m["Affine modulo 29 token"] := ["Custom", "Affine modulo 29 token"]
    m["Affine modulo 31 token"] := ["Custom", "Affine modulo 31 token"]
    m["Affine modulo 37 token"] := ["Custom", "Affine modulo 37 token"]
    m["Zeckendorf index"] := ["Custom", "Zeckendorf index"]
    m["Elias omega token"] := ["Custom", "Elias omega token"]
    m["Rice unary-binary token"] := ["Custom", "Rice unary-binary token"]
    m["Balanced quinary index"] := ["Custom", "Balanced quinary index"]
    m["Balanced senary index"] := ["Custom", "Balanced senary index"]
    m["Prime product index"] := ["Custom", "Prime product index"]
    m["Chinese remainder token"] := ["Custom", "Chinese remainder token"]
    m["Residue vector mod 2-3-5"] := ["Custom", "Residue vector mod 2-3-5"]
    m["Fibonacci word token"] := ["Custom", "Fibonacci word token"]
    m["Thue-Morse token"] := ["Custom", "Thue-Morse token"]
    m["ASCII base14 byte"] := ["Custom", "ASCII base14 byte"]
    m["ASCII base15 byte"] := ["Custom", "ASCII base15 byte"]
    m["ASCII base18 byte"] := ["Custom", "ASCII base18 byte"]
    m["ASCII base22 byte"] := ["Custom", "ASCII base22 byte"]
    m["ASCII base25 byte"] := ["Custom", "ASCII base25 byte"]
    m["ASCII base28 byte"] := ["Custom", "ASCII base28 byte"]
    m["ASCII base29 byte"] := ["Custom", "ASCII base29 byte"]
    m["ASCII base33 byte"] := ["Custom", "ASCII base33 byte"]
    m["ASCII base34 byte"] := ["Custom", "ASCII base34 byte"]
    m["ASCII base35 byte"] := ["Custom", "ASCII base35 byte"]
    m["UTF-8 C array token"] := ["Custom", "UTF-8 C array token"]
    m["UUID byte token"] := ["Custom", "UUID byte token"]
    m["GUID byte token"] := ["Custom", "GUID byte token"]
    m["IPv4 octet token"] := ["Custom", "IPv4 octet token"]
    m["IPv6 hextet token"] := ["Custom", "IPv6 hextet token"]
    m["DNS label token"] := ["Custom", "DNS label token"]
    m["INI hex token"] := ["Custom", "INI hex token"]
    m["TOML unicode token"] := ["Custom", "TOML unicode token"]
    m["YAML unicode token"] := ["Custom", "YAML unicode token"]
    m["CSV hex cell token"] := ["Custom", "CSV hex cell token"]
    m["QR numeric token"] := ["Custom", "QR numeric token"]
    m["GS1 AI token"] := ["Custom", "GS1 AI token"]
    m["Aztec binary token"] := ["Custom", "Aztec binary token"]
    m["PDF417 compact token"] := ["Custom", "PDF417 compact token"]
    m["DataMatrix C40 token"] := ["Custom", "DataMatrix C40 token"]
    m["Cherokee letters"] := ["Custom", "Cherokee letters"]
    m["Canadian syllabics"] := ["Custom", "Canadian syllabics"]
    m["Hiragana phonetic"] := ["Custom", "Hiragana phonetic"]
    m["Hangul jamo token"] := ["Custom", "Hangul jamo token"]
    m["Thai alphabet token"] := ["Custom", "Thai alphabet token"]
    m["Devanagari letters"] := ["Custom", "Devanagari letters"]
    m["Bengali letters"] := ["Custom", "Bengali letters"]
    m["Arabic abjad"] := ["Custom", "Arabic abjad"]
    m["Syriac letters"] := ["Custom", "Syriac letters"]
    m["Tifinagh letters"] := ["Custom", "Tifinagh letters"]
    m["Samaritan letters"] := ["Custom", "Samaritan letters"]
    m["Nabataean tokens"] := ["Custom", "Nabataean tokens"]
    m["Pahlavi tokens"] := ["Custom", "Pahlavi tokens"]
    m["Old Persian cuneiform"] := ["Custom", "Old Persian cuneiform"]
    m["Cypriot syllabary tokens"] := ["Custom", "Cypriot syllabary tokens"]
    m["Huffman fixed token"] := ["Custom", "Huffman fixed token"]
    m["LZW dictionary token"] := ["Custom", "LZW dictionary token"]
    m["BWT rotation token"] := ["Custom", "BWT rotation token"]
    m["Arithmetic toy interval"] := ["Custom", "Arithmetic toy interval"]
    m["Range coder toy token"] := ["Custom", "Range coder toy token"]
    m["Deflate block marker"] := ["Custom", "Deflate block marker"]
    m["Brotli meta token"] := ["Custom", "Brotli meta token"]
    m["Zstd sequence token"] := ["Custom", "Zstd sequence token"]
    m["RLE binary run token"] := ["Custom", "RLE binary run token"]
    m["Move-to-front rank token"] := ["Custom", "Move-to-front rank token"]
    m["Vigenere Pell stream"] := ["Custom", "Vigenere Pell stream"]
    m["Vigenere Jacobsthal stream"] := ["Custom", "Vigenere Jacobsthal stream"]
    m["Vigenere Padovan stream"] := ["Custom", "Vigenere Padovan stream"]
    m["Vigenere Tetranacci stream"] := ["Custom", "Vigenere Tetranacci stream"]
    m["Beaufort Catalan stream"] := ["Custom", "Beaufort Catalan stream"]
    m["Beaufort Bell stream"] := ["Custom", "Beaufort Bell stream"]
    m["Variant Beaufort Pell stream"] := ["Custom", "Variant Beaufort Pell stream"]
    m["Variant Beaufort Jacobsthal stream"] := ["Custom", "Variant Beaufort Jacobsthal stream"]
    m["Porta Fibonacci stream"] := ["Custom", "Porta Fibonacci stream"]
    m["Porta prime-gap stream"] := ["Custom", "Porta prime-gap stream"]
    m["Caesar Perrin stream"] := ["Custom", "Caesar Perrin stream"]
    m["Caesar Motzkin stream"] := ["Custom", "Caesar Motzkin stream"]
    m["Caesar Thue-Morse stream"] := ["Custom", "Caesar Thue-Morse stream"]
    m["Caesar Golomb stream"] := ["Custom", "Caesar Golomb stream"]
    m["Caesar bitcount stream"] := ["Custom", "Caesar bitcount stream"]
    m["Caesar digital-sum stream"] := ["Custom", "Caesar digital-sum stream"]
    m["Caesar modular inverse stream"] := ["Custom", "Caesar modular inverse stream"]
    m["Caesar quadratic residue stream"] := ["Custom", "Caesar quadratic residue stream"]
    m["Caesar power-of-two stream"] := ["Custom", "Caesar power-of-two stream"]
    m["Caesar factorial mod shift"] := ["Custom", "Caesar factorial mod shift"]
    m["Keyed alphabet Fibonacci"] := ["Custom", "Keyed alphabet Fibonacci"]
    m["Keyed alphabet prime"] := ["Custom", "Keyed alphabet prime"]
    m["Keyed alphabet triangular"] := ["Custom", "Keyed alphabet triangular"]
    m["Reverse-keyword substitution"] := ["Custom", "Reverse-keyword substitution"]
    m["Beaufort reciprocal alphabet"] := ["Custom", "Beaufort reciprocal alphabet"]
    m["Vigenere reciprocal alphabet"] := ["Custom", "Vigenere reciprocal alphabet"]
    m["Nihilist mod 100 token"] := ["Custom", "Nihilist mod 100 token"]
    m["Nihilist hex stream token"] := ["Custom", "Nihilist hex stream token"]
    m["Polybius row-major binary"] := ["Custom", "Polybius row-major binary"]
    m["Polybius column-major binary"] := ["Custom", "Polybius column-major binary"]
    m["Polybius knight coords"] := ["Custom", "Polybius knight coords"]
    m["Polybius spiral coords"] := ["Custom", "Polybius spiral coords"]
    m["Checkerboard Morse rows"] := ["Custom", "Checkerboard Morse rows"]
    m["Checkerboard NATO columns"] := ["Custom", "Checkerboard NATO columns"]
    m["Tap code Morse token"] := ["Custom", "Tap code Morse token"]
    m["Tap code binary token v2"] := ["Custom", "Tap code binary token v2"]
    m["Fractionated Morse numeric"] := ["Custom", "Fractionated Morse numeric"]
    m["Fractionated Morse base3"] := ["Custom", "Fractionated Morse base3"]
    m["Pollux binary 0-1-2"] := ["Custom", "Pollux binary 0-1-2"]
    m["Pollux emoji 0-1-2"] := ["Custom", "Pollux emoji 0-1-2"]
    m["Morbit binary pairs"] := ["Custom", "Morbit binary pairs"]
    m["Morbit ternary pairs"] := ["Custom", "Morbit ternary pairs"]
    m["Baconian Baudot"] := ["Custom", "Baconian Baudot"]
    m["Baconian five-bit binary"] := ["Custom", "Baconian five-bit binary"]
    m["Baconian quaternary tag"] := ["Custom", "Baconian quaternary tag"]
    m["A1Z26 mod 9"] := ["Custom", "A1Z26 mod 9"]
    m["A1Z26 mod 11"] := ["Custom", "A1Z26 mod 11"]
    m["A1Z26 Roman lowercase"] := ["Custom", "A1Z26 Roman lowercase"]
    m["A1Z26 Greek numerals"] := ["Custom", "A1Z26 Greek numerals"]
    m["A1Z26 resistor colors"] := ["Custom", "A1Z26 resistor colors"]
    m["ASCII base37 byte"] := ["Custom", "ASCII base37 byte"]
    m["ASCII base38 byte"] := ["Custom", "ASCII base38 byte"]
    m["ASCII base39 byte"] := ["Custom", "ASCII base39 byte"]
    m["ASCII base40 byte"] := ["Custom", "ASCII base40 byte"]
    m["ASCII base41 byte"] := ["Custom", "ASCII base41 byte"]
    m["ASCII base42 byte"] := ["Custom", "ASCII base42 byte"]
    m["ASCII base43 byte"] := ["Custom", "ASCII base43 byte"]
    m["ASCII base44 byte"] := ["Custom", "ASCII base44 byte"]
    m["UTF-8 octets bracketed"] := ["Custom", "UTF-8 octets bracketed"]
    m["UTF-16LE bytes bracketed"] := ["Custom", "UTF-16LE bytes bracketed"]
    m["Unicode plane token"] := ["Custom", "Unicode plane token"]
    m["HTML named alpha token"] := ["Custom", "HTML named alpha token"]
    m["TeX alphabet command"] := ["Custom", "TeX alphabet command"]
    m["LaTeX mathbb command"] := ["Custom", "LaTeX mathbb command"]
    m["LaTeX mathcal command"] := ["Custom", "LaTeX mathcal command"]
    m["PostScript glyph name"] := ["Custom", "PostScript glyph name"]
    m["QR alphanumeric value"] := ["Custom", "QR alphanumeric value"]
    m["Base45 byte token"] := ["Custom", "Base45 byte token"]
    m["Base58 byte token"] := ["Custom", "Base58 byte token"]
    m["Base91 byte token"] := ["Custom", "Base91 byte token"]
    m["Reed-Solomon toy syndrome"] := ["Custom", "Reed-Solomon toy syndrome"]
    m["Hamming parity syndrome"] := ["Custom", "Hamming parity syndrome"]
    m["BCH toy syndrome"] := ["Custom", "BCH toy syndrome"]
    m["ISBN letter checksum"] := ["Custom", "ISBN letter checksum"]
    m["EAN letter checksum"] := ["Custom", "EAN letter checksum"]
    m["Codabar alphabet token"] := ["Custom", "Codabar alphabet token"]
    m["Code39 full ASCII token"] := ["Custom", "Code39 full ASCII token"]
    m["Teleprinter shift token"] := ["Custom", "Teleprinter shift token"]
    m["SITOR bit token"] := ["Custom", "SITOR bit token"]
    m["Baudot Murray token compact"] := ["Custom", "Baudot Murray token compact"]

    ; v28 and later: guarantee every mode has at least a Custom/default preset.
    for _, mode in MODE_LIST {
        if !m.Has(mode)
            m[mode] := ["Custom", mode]
    }
    m["Caesar ROT5 digits classic"] := ["Custom", "Caesar ROT5 digits classic"]
    m["Caesar ROT18 alphanumeric classic"] := ["Custom", "Caesar ROT18 alphanumeric classic"]
    m["Caesar ROT25 inverse classic"] := ["Custom", "Caesar ROT25 inverse classic"]
    m["Polybius torch code Latin"] := ["Custom", "Polybius torch code Latin"]
    m["Polybius 6x6 military checkerboard"] := ["Custom", "Polybius 6x6 military checkerboard"]
    m["Trithemius recta Latin classic"] := ["Custom", "Trithemius recta Latin classic"]
    m["Trithemius progressive keyed recta"] := ["Custom", "Trithemius progressive keyed recta"]
    m["Alberti numeric indicator disk"] := ["Custom", "Alberti numeric indicator disk"]
    m["Alberti periodic indicator disk"] := ["Custom", "Alberti periodic indicator disk"]
    m["Porta disk diplomatic variant"] := ["Custom", "Porta disk diplomatic variant"]
    m["Della Porta reciprocal disk v2"] := ["Custom", "Della Porta reciprocal disk v2"]
    m["Bellaso cipher with countersign v3"] := ["Custom", "Bellaso cipher with countersign v3"]
    m["Vigenere running primer v2"] := ["Custom", "Vigenere running primer v2"]
    m["Vigenere Beaufort mixed alphabet v2"] := ["Custom", "Vigenere Beaufort mixed alphabet v2"]
    m["Beaufort army field key"] := ["Custom", "Beaufort army field key"]
    m["Gronsfeld Venetian numeric variant"] := ["Custom", "Gronsfeld Venetian numeric variant"]
    m["Autoclave cipher historical v2"] := ["Custom", "Autoclave cipher historical v2"]
    m["Beaufort autoclave historical"] := ["Custom", "Beaufort autoclave historical"]
    m["Kasiski keyed Vigenere variant"] := ["Custom", "Kasiski keyed Vigenere variant"]
    m["Bazeries number-key classic v2"] := ["Custom", "Bazeries number-key classic v2"]
    m["Chaocipher alphabet classic v2"] := ["Custom", "Chaocipher alphabet classic v2"]
    m["Phillips plaintext slide variant"] := ["Custom", "Phillips plaintext slide variant"]
    m["Phillips ciphertext slide variant"] := ["Custom", "Phillips ciphertext slide variant"]
    m["Doppelkasten checkerboard keyed"] := ["Custom", "Doppelkasten checkerboard keyed"]
    m["Digrafid German field style"] := ["Custom", "Digrafid German field style"]
    m["Nihilist checkerboard overadd v3"] := ["Custom", "Nihilist checkerboard overadd v3"]
    m["Nihilist columnar transposition style"] := ["Custom", "Nihilist columnar transposition style"]
    m["Bifid fractionating period 3"] := ["Custom", "Bifid fractionating period 3"]
    m["Bifid fractionating period 9"] := ["Custom", "Bifid fractionating period 9"]
    m["Trifid fractionating period 3"] := ["Custom", "Trifid fractionating period 3"]
    m["Trifid fractionating period 9"] := ["Custom", "Trifid fractionating period 9"]
    m["ADFGX keyed Polybius field"] := ["Custom", "ADFGX keyed Polybius field"]
    m["ADFGVX alphanumeric field v2"] := ["Custom", "ADFGVX alphanumeric field v2"]
    m["Monome-Dinome French army variant"] := ["Custom", "Monome-Dinome French army variant"]
    m["Straddling checkerboard decimal variant"] := ["Custom", "Straddling checkerboard decimal variant"]
    m["VIC sequential transposition style"] := ["Custom", "VIC sequential transposition style"]
    m["VIC agent pad groups v2"] := ["Custom", "VIC agent pad groups v2"]
    m["Interrupted columnar WWI variant"] := ["Custom", "Interrupted columnar WWI variant"]
    m["Myszkowski commercial variant"] := ["Custom", "Myszkowski commercial variant"]
    m["Double columnar agent variant"] := ["Custom", "Double columnar agent variant"]
    m["Rail fence 6-rail classic"] := ["Custom", "Rail fence 6-rail classic"]
    m["Rail fence 7-rail classic"] := ["Custom", "Rail fence 7-rail classic"]
    m["Turning grille 6x6 Austro-Hungarian"] := ["Custom", "Turning grille 6x6 Austro-Hungarian"]
    m["Cardan grille Venetian style"] := ["Custom", "Cardan grille Venetian style"]
    m["AMSCO period-2 classic"] := ["Custom", "AMSCO period-2 classic"]
    m["Cadenus ACA variant B"] := ["Custom", "Cadenus ACA variant B"]
    m["Gromark keyed primer variant"] := ["Custom", "Gromark keyed primer variant"]
    m["Ragbaby period-word start variant"] := ["Custom", "Ragbaby period-word start variant"]
    m["Nicodemus transposition Vigenere v2"] := ["Custom", "Nicodemus transposition Vigenere v2"]
    m["Seriated Playfair period 8"] := ["Custom", "Seriated Playfair period 8"]
    m["Portax ACA variant"] := ["Custom", "Portax ACA variant"]
    m["Slidefair ACA variant v2"] := ["Custom", "Slidefair ACA variant v2"]
    m["Four-square Delastelle variant v2"] := ["Custom", "Four-square Delastelle variant v2"]
    m["Two-square German field variant"] := ["Custom", "Two-square German field variant"]
    m["Tri-square ACA classic"] := ["Custom", "Tri-square ACA classic"]
    m["Homophonic nomenclator 1400s"] := ["Custom", "Homophonic nomenclator 1400s"]
    m["Beale variant book cipher"] := ["Custom", "Beale variant book cipher"]
    m["Dorabella symbol alphabet v2"] := ["Custom", "Dorabella symbol alphabet v2"]
    m["Freemason pigpen X-grid"] := ["Custom", "Freemason pigpen X-grid"]
    m["Templar pigpen dotted cross"] := ["Custom", "Templar pigpen dotted cross"]
    m["Rosicrucian dotted grid"] := ["Custom", "Rosicrucian dotted grid"]
    m["Zodiac 408 homophonic table v3"] := ["Custom", "Zodiac 408 homophonic table v3"]
    m["Zodiac 340 diagonal read style"] := ["Custom", "Zodiac 340 diagonal read style"]
    m["Copiale homophonic codebook"] := ["Custom", "Copiale homophonic codebook"]
    m["Voynich Currier glyph token"] := ["Custom", "Voynich Currier glyph token"]
    m["Navajo code talker word v2"] := ["Custom", "Navajo code talker word v2"]
    m["Choctaw code talker token"] := ["Custom", "Choctaw code talker token"]
    m["Q-code maritime token"] := ["Custom", "Q-code maritime token"]
    m["Z-code military token"] := ["Custom", "Z-code military token"]
    m["Ten-code police radio token"] := ["Custom", "Ten-code police radio token"]
    m["NATO brevity code token v2"] := ["Custom", "NATO brevity code token v2"]
    m["ICS flag hoist two-letter"] := ["Custom", "ICS flag hoist two-letter"]
    m["Semaphore field flag token"] := ["Custom", "Semaphore field flag token"]
    m["Wigwag single-flag token"] := ["Custom", "Wigwag single-flag token"]
    m["American Morse spaced token"] := ["Custom", "American Morse spaced token"]
    m["International Morse spaced token"] := ["Custom", "International Morse spaced token"]
    m["Baudot ITA2 figures-letters field"] := ["Custom", "Baudot ITA2 figures-letters field"]
    m["Murray code teleprinter field"] := ["Custom", "Murray code teleprinter field"]
    m["Vernam Baudot XOR field"] := ["Custom", "Vernam Baudot XOR field"]
    m["OTP subtractive letter groups"] := ["Custom", "OTP subtractive letter groups"]
    m["OTP additive number groups"] := ["Custom", "OTP additive number groups"]
    m["Numbers station Cyrillic style token"] := ["Custom", "Numbers station Cyrillic style token"]
    m["Commercial codebook four-letter"] := ["Custom", "Commercial codebook four-letter"]
    m["Slater code word variant"] := ["Custom", "Slater code word variant"]
    m["Bentley code word variant"] := ["Custom", "Bentley code word variant"]
    m["ABC code word variant"] := ["Custom", "ABC code word variant"]
    m["Zimmermann cable code variant"] := ["Custom", "Zimmermann cable code variant"]
    m["Diplomatic four-digit book code"] := ["Custom", "Diplomatic four-digit book code"]
    m["Diplomatic five-letter book code"] := ["Custom", "Diplomatic five-letter book code"]
    m["Weather SYNOP code token"] := ["Custom", "Weather SYNOP code token"]
    m["Naval signal book token"] := ["Custom", "Naval signal book token"]
    m["Army map grid code token"] := ["Custom", "Army map grid code token"]
    m["SOE poem transposition v2"] := ["Custom", "SOE poem transposition v2"]
    m["Resistance grille code token"] := ["Custom", "Resistance grille code token"]
    m["Silk code miniature map token"] := ["Custom", "Silk code miniature map token"]
    m["Enigma M3 army daily key"] := ["Custom", "Enigma M3 army daily key"]
    m["Enigma M4 weather key"] := ["Custom", "Enigma M4 weather key"]
    m["Enigma Abwehr G style v2"] := ["Custom", "Enigma Abwehr G style v2"]
    m["Typex Mark VI style"] := ["Custom", "Typex Mark VI style"]
    m["SIGABA CSP-2900 style"] := ["Custom", "SIGABA CSP-2900 style"]
    m["NEMA training key style"] := ["Custom", "NEMA training key style"]
    m["Fialka Latin wheel style"] := ["Custom", "Fialka Latin wheel style"]
    m["KL-7 training key style"] := ["Custom", "KL-7 training key style"]
    m["Hagelin C-36 pin-lug style"] := ["Custom", "Hagelin C-36 pin-lug style"]
    m["Hagelin CD-57 pocket style v2"] := ["Custom", "Hagelin CD-57 pocket style v2"]
    m["Siemens T52ca style"] := ["Custom", "Siemens T52ca style"]
    m["Lorenz SZ42c style"] := ["Custom", "Lorenz SZ42c style"]
    m["Purple diplomatic 1939 style"] := ["Custom", "Purple diplomatic 1939 style"]
    m["Red-Orange Japanese machine style"] := ["Custom", "Red-Orange Japanese machine style"]
    m["Rockex II tape style"] := ["Custom", "Rockex II tape style"]
    m["KW-7 ORESTES stream style"] := ["Custom", "KW-7 ORESTES stream style"]
    for _, v37Mode in V37ModeNames()
        m[v37Mode] := ["Custom", v37Mode, v37Mode . " — random key"]
    for _, v38Mode in V38ModeNames()
        m[v38Mode] := ["Custom", v38Mode, v38Mode . " — random key"]
    for _, v39Mode in V39ModeNames()
        m[v39Mode] := ["Custom", v39Mode, v39Mode . " — random key"]
    for _, v40Mode in V40ModeNames()
        m[v40Mode] := ["Custom", v40Mode, v40Mode . " — random key"]
    m["Keyed alphabet Caesar"] := ["Custom", "Keyed alphabet Caesar +1", "Keyed alphabet Caesar +3", "Keyed alphabet Caesar +5", "Keyed alphabet Caesar +13", "Keyed alphabet Caesar random"]
    for _, autoMode in MODE_LIST {
        if !m.Has(autoMode)
            m[autoMode] := ["Custom", autoMode]
    }
    AddCollapsedSettingPresets(m)
    RemoveHiddenPresetEntries(m)
    return m
}

AddPresetIfMissing(list, item) {
    for _, existing in list {
        if existing = item
            return
    }
    list.Push(item)
}

AddCollapsedSettingPresets(m) {
    groups := Map()
    groups["ADFGVX"] := [
        "ADFGVX 6x6 coords",
        "ADFGVX alphanumeric field v2",
        "ADFGVX alphanumeric square v5",
        "ADFGVX column key classic",
        "ADFGVX escaped",
        "ADFGVX field cipher",
        "ADFGVX fractionation classic",
        "ADFGVX German 1918",
        "ADFGVX German Army 1918 v3",
        "ADFGVX German field 1918 v4",
        "ADFGVX mixed square classic",
        "ADFGVX Nebel 1918 worksheet",
        "ADFGVX Nebel alphanumeric v2",
        "ADFGVX Nebel army worksheet v2",
        "ADFGVX Nebel classic",
        "ADFGVX numeric labels",
        "ADFGVX phone square",
        "ADFGVX radio traffic variant",
        "ADFGVX reversed square",
        "ADFGVX six-symbol field v4",
        "ADFGVX spaced"
    ]
    groups["ADFGX"] := [
        "ADFGX columnar classic v2",
        "ADFGX columnar transposition v4",
        "ADFGX field cipher",
        "ADFGX fractionation classic",
        "ADFGX German 1918",
        "ADFGX German Army 1918 v3",
        "ADFGX German field 1918 v4",
        "ADFGX mixed Polybius square v5",
        "ADFGX Morse square",
        "ADFGX Nebel 1918 worksheet",
        "ADFGX Nebel army worksheet v2",
        "ADFGX Nebel classic",
        "ADFGX Nebel field square v2",
        "ADFGX numeric labels",
        "ADFGX reversed square",
        "ADFGX spaced",
        "ADFGX Western Front variant",
        "Morse fractionated ADFGX",
        "UBCHI ADFGX double columnar",
        "UBCHI pre-ADFGX transposition v3"
    ]
    groups["Affine"] := [
        "Affine cipher classic",
        "Affine Decimation 11 classic",
        "Affine Decimation 7 classic",
        "Affine family token",
        "Affine modulo 29 token",
        "Affine modulo 31 token",
        "Affine modulo 37 token",
        "Affine with key shift",
        "Multiplicative cipher x11",
        "Multiplicative cipher x17",
        "Multiplicative cipher x25",
        "Multiplicative cipher x3",
        "Multiplicative cipher x5",
        "Multiplicative cipher x7",
        "Progressive Affine",
        "Progressive Decimation"
    ]
    groups["Alberti disk"] := [
        "Alberti disk 1467",
        "Alberti disk changing indicator",
        "Alberti disk fixed index v4",
        "Alberti disk index letter system",
        "Alberti disk lowercase ring v3",
        "Alberti disk movable ring v2",
        "Alberti disk moving index every four",
        "Alberti disk periodic switch v3",
        "Alberti disk plaintext indicator",
        "Alberti disk progressive index v4",
        "Alberti numeric indicator disk",
        "Alberti numeric shift indicator v2",
        "Alberti periodic indicator disk",
        "Alberti progressive disk",
        "Alberti shifting alphabet 1467"
    ]
    groups["AMSCO block"] := [
        "AMSCO ACA cipher",
        "AMSCO alternating 1-2",
        "AMSCO classic",
        "AMSCO German variant",
        "AMSCO irregular transposition classic",
        "AMSCO irregular transposition v2",
        "AMSCO period-2 classic",
        "AMSCO transposition ACA v3"
    ]
    groups["Atbash"] := [
        "Alternating Atbash",
        "Atbash biblical Hebrew style v2",
        "Atbash Caesar shift",
        "Atbash Hebrew classic",
        "Atbash Hebrew square script v2",
        "Atbash then Vigenere",
        "Autokey Atbash",
        "Beaufort Atbash hybrid",
        "Hebrew Atbash original alphabet",
        "Printable ASCII Atbash",
        "Progressive Atbash stream",
        "Running Atbash key",
        "Variant Beaufort Atbash hybrid",
        "Vigenere Atbash hybrid",
        "Vigenere plus Atbash",
        "Vigenere then Atbash"
    ]
    groups["Autokey Beaufort"] := [
        "Variant Beaufort Autokey"
    ]
    groups["Autokey Vigenere"] := [
        "Blaise de Vigenere autokey",
        "Vigenere 1586 autokey",
        "Vigenere autokey 1586 original",
        "Vigenere autokey historical v2",
        "Vigenere autokey original v4"
    ]
    groups["Bazeries cylinder style"] := [
        "Bazeries cylinder 20 disk v3",
        "Bazeries cylinder classic",
        "Bazeries cylinder numeric key v2"
    ]
    groups["Beaufort"] := [
        "Beaufort Admiralty cipher",
        "Beaufort Admiralty cipher v3",
        "Beaufort Admiralty reciprocal v2",
        "Beaufort army field key",
        "Beaufort autoclave",
        "Beaufort autoclave field v2",
        "Beaufort autoclave historical",
        "Beaufort Bell stream",
        "Beaufort Catalan stream",
        "Beaufort Fibonacci stream",
        "Beaufort keyed alphabet",
        "Beaufort naval reciprocal 1857 v3",
        "Beaufort naval reciprocal 1915",
        "Beaufort naval reciprocal v2",
        "Beaufort naval table 1857",
        "Beaufort prime stream",
        "Beaufort reciprocal alphabet",
        "Beaufort reciprocal classic",
        "Beaufort reversed alphabet",
        "Beaufort Royal Navy",
        "Beaufort Royal Navy table v4",
        "Beaufort square stream",
        "Beaufort triangular stream",
        "Interrupted Beaufort",
        "Keyed Beaufort",
        "Printable Beaufort",
        "Progressive Beaufort",
        "Progressive key Beaufort",
        "Running key Beaufort",
        "Vigenere autoclave Beaufort style",
        "Vigenere Beaufort hybrid ACA",
        "Vigenere Beaufort mixed alphabet v2",
        "Vigenere Beaufort reciprocal",
        "Vigenere Beaufort reciprocal field",
        "Vigenere Beaufort reciprocal mix v2",
        "Vigenere Beaufort table 1710",
        "Vigenere Beaufort variant historical"
    ]
    groups["Bellaso"] := [
        "Bellaso 1553 reciprocal",
        "Bellaso 1564 countersign",
        "Bellaso autokey countersign style",
        "Bellaso cipher with countersign v3",
        "Bellaso countersign cipher",
        "Bellaso countersign long key",
        "Bellaso countersign reciprocal v4",
        "Bellaso la cifra del Sig Giovan v2",
        "Bellaso progressive countersign",
        "Bellaso reciprocal 1555 variant",
        "Bellaso reciprocal alphabet 1564",
        "Bellaso reciprocal countersign v5",
        "Bellaso reciprocal table",
        "Bellaso reciprocal table 1553 v2",
        "Porta Bellaso table"
    ]
    groups["Bifid pairs"] := [
        "Bifid 6x6 pairs",
        "Bifid cipher period 7",
        "Bifid coordinate stream",
        "Bifid Delastelle",
        "Bifid Delastelle 1895 period 6",
        "Bifid Delastelle no-period classic",
        "Bifid Delastelle period 5 v3",
        "Bifid Delastelle period 7",
        "Bifid Delastelle period 7 v2",
        "Bifid fractionating period 3",
        "Bifid fractionating period 9",
        "Bifid numeric fraction",
        "Bifid period 10 Delastelle",
        "Bifid period 5 classic",
        "Bifid raw coords",
        "Bifid split token",
        "CM Bifid ACA",
        "CM Bifid ACA variant v2",
        "Delastelle Bifid 1895 army variant",
        "Delastelle Bifid classic period 5",
        "Seriated Bifid ACA",
        "Seriated Bifid ACA period v2",
        "Twin Bifid pairs"
    ]
    groups["Cadenus block"] := [
        "Cadenus 25-row ACA",
        "Cadenus 25-row field variant",
        "Cadenus ACA 25-row",
        "Cadenus ACA alphabetic v3",
        "Cadenus ACA classic",
        "Cadenus ACA v2",
        "Cadenus ACA variant B",
        "Cadenus alphabetic transposition v2",
        "Cadenus alphabetic transposition v4",
        "Cadenus periodic transposition v2",
        "Cadenus transposition variant"
    ]
    groups["Caesar"] := [
        "Affine Caesar 5x plus 8 classic",
        "Augustus Caesar shift variant",
        "Augustus cipher no-A shift",
        "Augustus cipher variant v2",
        "Augustus shift variant",
        "Autokey Caesar stream",
        "Caesar alphabet wrap field v3",
        "Caesar Bell shift",
        "Caesar bitcount stream",
        "Caesar Catalan shift",
        "Caesar cipher Augustus",
        "Caesar cipher classic",
        "Caesar cipher wheel classic",
        "Caesar Collatz shift",
        "Caesar cosine wave shift",
        "Caesar digital-sum stream",
        "Caesar factorial mod shift",
        "Caesar Gallic War shift v2",
        "Caesar Golomb stream",
        "Caesar legion field shift",
        "Caesar modular inverse stream",
        "Caesar Motzkin shift",
        "Caesar Motzkin stream",
        "Caesar Perrin shift",
        "Caesar Perrin stream",
        "Caesar power-of-two stream",
        "Caesar quadratic residue stream",
        "Caesar reverse alphabet shift",
        "Caesar ROT18 alphanumeric classic",
        "Caesar ROT25 inverse classic",
        "Caesar ROT5 digits classic",
        "Caesar sawtooth shift",
        "Caesar sine wave shift",
        "Caesar square wave shift",
        "Caesar Suetonius variant",
        "Caesar Thue-Morse stream",
        "Caesar triangular wave shift",
        "Jacobsthal Caesar shift",
        "Padovan Caesar shift",
        "Pell Caesar shift",
        "Prime gap Caesar shift",
        "Roman Caesar dispatch shift II",
        "Roman Caesar dispatch shift IV",
        "Roman Caesar dispatch shift VI",
        "Roman Caesar military watchword",
        "Runic Caesar stave shift",
        "Runic Caesar wheel v2",
        "Tetranacci Caesar shift",
        "Word Caesar"
    ]
    groups["Columnar transposition block"] := [
        "Alternating columnar block",
        "AMSCO irregular columnar v4",
        "Columnar army field cipher",
        "Columnar cadenus mixed",
        "Columnar complete classic",
        "Columnar disrupted field v2",
        "Columnar irregular classic",
        "Columnar transposition classic",
        "Columnar transposition complete v2",
        "Columnar transposition incomplete v2",
        "Columnar transposition WWI army",
        "Complete columnar block",
        "Complete columnar field cipher",
        "Complete columnar military v3",
        "Disrupted transposition ACA v3",
        "Disrupted transposition block",
        "Disrupted transposition classic",
        "Incomplete columnar block",
        "Incomplete columnar field cipher",
        "Incomplete columnar military v3",
        "Interrupted columnar transposition",
        "Interrupted columnar WWI variant",
        "VIC disrupted transposition classic",
        "VIC disrupted transposition v2",
        "VIC disrupted transposition v3",
        "VIC disrupted transposition v4"
    ]
    groups["Diana cipher"] := [
        "Diana cryptosystem OTP v3",
        "Diana one-time pad classic",
        "Diana OTP training sheet v2",
        "Diana reciprocal",
        "Diana reciprocal OTP sheet v3",
        "Diana reciprocal pad worksheet"
    ]
    groups["Double columnar block"] := [
        "AMSCO double columnar v2",
        "Double columnar agent variant",
        "Double columnar French resistance",
        "Double columnar German army v3",
        "Double columnar resistance v4",
        "Double columnar SOE variant",
        "Double columnar WW2",
        "Double columnar WW2 agent v4",
        "Double transposition agent classic",
        "Double transposition agent style",
        "Double transposition military",
        "Double transposition SOE v5",
        "UBCHI columnar transposition",
        "UBCHI double transposition",
        "UBCHI German army 1914 v4",
        "UBCHI German double transposition v2",
        "UBCHI pre-Nebel field v2",
        "VIC double transposition v4"
    ]
    groups["Double Playfair pairs"] := [
        "Double Playfair British variant",
        "Double Playfair classic",
        "Double Playfair German worksheet",
        "Double Playfair Wehrmacht",
        "Double Playfair Wehrmacht v2",
        "Double Playfair WW1"
    ]
    groups["Enigma M3"] := [
        "Enigma I army key sheet v2",
        "Enigma I Heer key v3",
        "Enigma I Luftwaffe key v3",
        "Enigma I Wehrmacht live",
        "Enigma I Wehrmacht v4",
        "Enigma M3 army daily key",
        "Enigma M3 Kriegsmarine key v3",
        "Enigma M3 Luftwaffe key live",
        "Enigma M3 naval bigram key",
        "Enigma M3 naval style live",
        "Enigma M3 Navy v4",
        "Enigma M3 Wehrmacht style"
    ]
    groups["Enigma M4"] := [
        "Enigma M4 officer key live",
        "Enigma M4 shark style live",
        "Enigma M4 Triton Shark v3",
        "Enigma M4 Triton style",
        "Enigma M4 Triton weather key",
        "Enigma M4 U-boat Kurzsignal",
        "Enigma M4 U-boat shark key",
        "Enigma M4 U-boat v4",
        "Enigma M4 weather key"
    ]
    groups["Fleissner grille block"] := [
        "Fleissner 8x8 grille",
        "Fleissner grille 6x6",
        "Fleissner grille 6x6 v2",
        "Fleissner grille 8x8 classic",
        "Fleissner grille WWI 6x6 v3",
        "Fleissner turning grille 4x4 v4",
        "Fleissner turning grille 6x6 v4",
        "Fleissner turning grille 8x8",
        "Fleissner turning grille classic"
    ]
    groups["Four-square pairs"] := [
        "Delastelle Four-square military",
        "Four-square army variant",
        "Four-square Delastelle",
        "Four-square Delastelle 1902 v3",
        "Four-square Delastelle army v2",
        "Four-square Delastelle variant v2",
        "Four-square French army",
        "Four-square French classic",
        "Foursquare 5x5 classic"
    ]
    groups["Grille mask block"] := [
        "Cardan grille 1550 mask v2",
        "Cardan grille 16th century",
        "Cardan grille 6x6 classic",
        "Cardan grille classic",
        "Cardan grille diplomatic 6x6",
        "Cardan grille literary cipher",
        "Cardan grille literary mask",
        "Cardan grille Renaissance",
        "Cardan grille Renaissance v3",
        "Cardan grille Venetian style",
        "Cardano grille letter mask v2",
        "Cardano literary grille v3",
        "Turning grille 4x4 classic",
        "Turning grille 6x6 Austro-Hungarian",
        "Turning grille Cardan 4x4",
        "Turning grille diplomatic square v3",
        "Turning grille field cipher",
        "Turning grille four-rotation v2",
        "Turning grille Russian style",
        "Turning grille WWI German v4"
    ]
    groups["Gronsfeld"] := [
        "Autokey Gronsfeld",
        "Count Gronsfeld cipher",
        "Gronsfeld 1817",
        "Gronsfeld aristocrat classic",
        "Gronsfeld autokey",
        "Gronsfeld Bavarian diplomatic v3",
        "Gronsfeld count key worksheet",
        "Gronsfeld count numeral key v4",
        "Gronsfeld courier key",
        "Gronsfeld decimal field key v3",
        "Gronsfeld decimal key classic",
        "Gronsfeld diplomatic numerals v2",
        "Gronsfeld numeric aristocrat",
        "Gronsfeld numeric primer v3",
        "Gronsfeld reversed alphabet",
        "Gronsfeld Venetian numeric variant",
        "Reciprocal Gronsfeld"
    ]
    groups["Jefferson disk"] := [
        "Jefferson wheel 1795 variant",
        "Jefferson wheel 36-disk v2",
        "Jefferson wheel cipher classic",
        "Jefferson wheel random disk order",
        "Jefferson-Bazeries cylinder",
        "Jefferson-Bazeries wheel v3"
    ]
    groups["Keyed ADFGX"] := [
        "ADFGX keyed Polybius field"
    ]
    groups["Keyed Caesar"] := [
        "Caesar keyed stream"
    ]
    groups["Keyed Polybius square"] := [
        "Keyed Polybius 0-4",
        "Keyed Polybius A-E"
    ]
    groups["M-209 Hagelin style"] := [
        "Hagelin M-209 converter v5",
        "Hagelin M-209 live",
        "Hagelin M-209 lug cage style",
        "Hagelin M-209 lug pattern v2",
        "Hagelin M-209 lug pin v2",
        "Hagelin M-209 pin cage v4",
        "M-209 converter live",
        "M-209 lug cage Army v3",
        "M-209 pinwheel field v3",
        "M-209-B converter live",
        "M-209-B field converter v2"
    ]
    groups["M-94 cylinder style"] := [
        "M-94 Army cylinder 25 wheel v3",
        "M-94 Army wheel daily offset",
        "M-94 US Army classic",
        "US Army M-94 strip variant"
    ]
    groups["Myszkowski transposition block"] := [
        "Myszkowski ACA cipher",
        "Myszkowski classic",
        "Myszkowski commercial variant",
        "Myszkowski repeated keyword v2",
        "Myszkowski repeated keyword v4",
        "Myszkowski repeated letters v2",
        "Myszkowski repeated-key classic",
        "Myszkowski transposition ACA v2",
        "Myszkowski transposition ACA v3",
        "Myszkowski transposition classic v5",
        "Myszkowski transposition field"
    ]
    groups["NATO words"] := [
        "Brevity code NATO tactical v3",
        "Checkerboard NATO columns",
        "NATO ACP-131 brevity token",
        "NATO brevity code token v2",
        "NATO brevity code v4",
        "NATO brevity codeword v2",
        "NATO brevity word group",
        "NATO compact",
        "NATO initials only",
        "NATO spelling alphabet official"
    ]
    groups["Nihilist substitution"] := [
        "Checkerboard Nihilist classic",
        "Checkerboard nihilist overadd",
        "Nihilist checkerboard overadd v3",
        "Nihilist checkerboard prison v5",
        "Nihilist checkerboard prisoner",
        "Nihilist cipher overaddition v2",
        "Nihilist columnar transposition style",
        "Nihilist fractionation classic",
        "Nihilist hex stream token",
        "Nihilist keyed hex",
        "Nihilist keyed number",
        "Nihilist mod 100 token",
        "Nihilist periodic key",
        "Nihilist plain coordinate",
        "Nihilist plus key stream",
        "Nihilist product token",
        "Nihilist Russian numbers 1880",
        "Nihilist substitution classic",
        "Nihilist substitution overadd v4",
        "Nihilist substitution overadd v5",
        "Nihilist substitution prison v4",
        "Nihilist substitution Russian",
        "Nihilist substitution Soviet",
        "Nihilist transposition ACA",
        "Nihilist transposition checkerboard v2",
        "Nihilist transposition classic",
        "Nihilist transposition classic v4",
        "Nihilist transposition Russian",
        "Nihilist transposition Siberian v3",
        "Nihilist zero padded",
        "Russian nihilist cipher v2",
        "Russian Nihilist prison code v3"
    ]
    groups["Playfair 6x6 pairs"] := [
        "Playfair 6x6 alphanumeric classic",
        "Playfair German 6x6",
        "Playfair German 6x6 field v2",
        "Playfair RAAF 6x6"
    ]
    groups["Playfair pairs"] := [
        "Lyon Playfair variant field",
        "Playfair 5x5 classic",
        "Playfair Australian Army",
        "Playfair Boer War field cipher",
        "Playfair British Army",
        "Playfair British field manual v2",
        "Playfair digraph marker",
        "Playfair German army 6x6 v3",
        "Playfair Lord Lyon",
        "Playfair Lord Playfair 1854 v2",
        "Playfair naval bigram key v3",
        "Playfair naval digraph v2",
        "Playfair Q omitted pairs",
        "Playfair WWI trench cipher",
        "Playfair WWII Australian field",
        "Wheatstone cryptograph alphabet v2",
        "Wheatstone cryptograph disk v3",
        "Wheatstone cryptograph rotor",
        "Wheatstone double-square classic",
        "Wheatstone Playfair",
        "Wheatstone Playfair digraph 1854",
        "Wheatstone-Playfair digraph v2"
    ]
    groups["Polybius square"] := [
        "Checkerboard 6x6 coords",
        "Checkerboard coordinates",
        "Checkerboard hex coords",
        "Checkerboard keyboard coords",
        "Checkerboard phone coords",
        "Fractionated Polybius token",
        "Greek Polybius naval beacon",
        "Greek Polybius torch two-square",
        "Nihilist Polybius classic",
        "Nihilist Polybius overadditive",
        "Polybius 0-based keyed",
        "Polybius 13x2",
        "Polybius 4x7",
        "Polybius 6x6",
        "Polybius 6x6 military checkerboard",
        "Polybius 7x4",
        "Polybius barcode token",
        "Polybius binary coords",
        "Polybius checker 0-4",
        "Polybius checker A-E",
        "Polybius checkerboard classic",
        "Polybius checkerboard military v5",
        "Polybius chess coords",
        "Polybius column letters",
        "Polybius column-major binary",
        "Polybius columnar block",
        "Polybius fire-signal square",
        "Polybius Greek labels",
        "Polybius knight coords",
        "Polybius letter coords keyed",
        "Polybius mixed 6x6 keyed",
        "Polybius Morse labels",
        "Polybius NATO coords",
        "Polybius planet labels",
        "Polybius prisoners square",
        "Polybius reversed",
        "Polybius Roman labels",
        "Polybius row letters",
        "Polybius row-major binary",
        "Polybius spiral coords",
        "Polybius square Greek classic",
        "Polybius symbol coords",
        "Polybius torch code Latin",
        "Polybius torch relay token v2",
        "Polybius torch telegraph",
        "Polybius zodiac labels"
    ]
    groups["Porta"] := [
        "Della Porta cipher disk v3",
        "Della Porta classic",
        "Della Porta disk",
        "Della Porta disk cipher",
        "Della Porta natural magic disk v2",
        "Della Porta reciprocal alphabet",
        "Della Porta reciprocal disk v2",
        "Porta 1563 table",
        "Porta Autokey",
        "Porta cipher table Naples 1563",
        "Porta digraph table 1563 v2",
        "Porta disk classic",
        "Porta disk diplomatic variant",
        "Porta disk reciprocal v4",
        "Porta Fibonacci stream",
        "Porta key-table variant",
        "Porta keyword table classic v2",
        "Porta numeric table",
        "Porta polyalphabetic 1563",
        "Porta polyalphabetic 1563 variant",
        "Porta polyalphabetic reciprocal v3",
        "Porta prime-gap stream",
        "Porta reciprocal 1563",
        "Porta reciprocal digraph",
        "Porta reciprocal field table",
        "Porta reverse table",
        "Porta table 13 alphabets v2",
        "Porta wheel alphabet v2",
        "Portax ACA cipher",
        "Portax ACA digraph cipher",
        "Portax ACA variant",
        "Portax digraph ACA v2",
        "Portax slide cipher v2"
    ]
    groups["Progressive Porta"] := [
        "Porta progressive reverse",
        "Porta progressive table classic"
    ]
    groups["Quagmire I"] := [
        "Quagmire I ACA classic",
        "Quagmire I ACA standard v4",
        "Quagmire I army style",
        "Quagmire I K1-K2 indicator",
        "Quagmire I keyed indicator v3",
        "Quagmire I mixed alphabet ACA v2"
    ]
    groups["Quagmire II"] := [
        "Quagmire II ACA classic",
        "Quagmire II ACA standard v4",
        "Quagmire II army style",
        "Quagmire II K1-K2 indicator",
        "Quagmire II keyed indicator v3",
        "Quagmire II mixed alphabet ACA v2"
    ]
    groups["Quagmire III"] := [
        "Quagmire III ACA classic",
        "Quagmire III ACA standard v4",
        "Quagmire III army style",
        "Quagmire III K1-K2 indicator",
        "Quagmire III keyed indicator v3",
        "Quagmire III mixed alphabet ACA v2"
    ]
    groups["Quagmire IV"] := [
        "Quagmire IV ACA classic",
        "Quagmire IV ACA standard v4",
        "Quagmire IV army style",
        "Quagmire IV K1-K2 indicator",
        "Quagmire IV keyed indicator v3",
        "Quagmire IV mixed alphabet ACA v2"
    ]
    groups["Rail fence block"] := [
        "Rail fence 2-rail classic",
        "Rail fence 3-rail classic",
        "Rail fence 4-rail classic",
        "Rail fence 5-rail classic",
        "Rail fence 6-rail classic",
        "Rail fence 7-rail classic",
        "Rail fence offset 3 rail v2",
        "Rail fence offset ACA",
        "Rail fence offset classic",
        "Rail fence offset military",
        "Rail fence offset Redefence v4",
        "Rail fence spaces block",
        "Rail fence telegraph v3",
        "Rail fence W pattern classic",
        "Rail fence zigzag ancient v4",
        "Rail fence zigzag classic",
        "Rail fence zigzag railway v2",
        "Redefence ACA cipher",
        "Redefence ACA rail cipher",
        "Redefence cipher ACA",
        "Redefence rail cipher v2",
        "Redefence rail offset block",
        "Redefence rail offset classic",
        "Redefence rail offset v3"
    ]
    groups["ROT13"] := [
        "Mixed alphabet ROT13",
        "ROT13 then Atbash",
        "ROT13 Usenet classic"
    ]
    groups["ROT47"] := [
        "Progressive ROT47 printable",
        "ROT47 printable classic",
        "ROT47 teleprinter printable v2",
        "ROT47 teletype printable v2"
    ]
    groups["Route cipher block"] := [
        "Confederate route cipher dispatch",
        "Route cipher boustrophedon field v3",
        "Route cipher boustrophedon military",
        "Route cipher clockwise spiral",
        "Route cipher counterclockwise spiral",
        "Route cipher diagonal military",
        "Route cipher grille",
        "Route cipher Hindenburg trench",
        "Route cipher inward spiral v2",
        "Route cipher outward spiral v2",
        "Route cipher snake route",
        "Route cipher spiral clockwise v2",
        "Route cipher spiral field v3",
        "Route cipher spiral inward classic",
        "Route cipher spiral military",
        "Route cipher spiral outward classic"
    ]
    groups["Running Key Vigenere"] := [
        "Vigenere running key classic",
        "Vigenere running key newspaper",
        "Vigenere running primer",
        "Vigenere running primer v2",
        "Vigenere running-key field v3"
    ]
    groups["Scytale transposition"] := [
        "Scytale Greek army variant",
        "Scytale Greek staff v3",
        "Scytale parchment strip v4",
        "Scytale Spartan classic",
        "Scytale Spartan courier v5",
        "Scytale Spartan strip v2",
        "Spartan scytale classic",
        "Spartan scytale courier strip v5"
    ]
    groups["Seriated Playfair pairs"] := [
        "Seriated Playfair ACA",
        "Seriated Playfair ACA period v2",
        "Seriated Playfair classic",
        "Seriated Playfair period 10",
        "Seriated Playfair period 6",
        "Seriated Playfair period 8"
    ]
    groups["Swagman block"] := [
        "Swagman ACA cipher",
        "Swagman ACA v2",
        "Swagman classic",
        "Swagman permutation classic",
        "Swagman route ACA v3",
        "Swagman route transposition v2",
        "Swagman route transposition v4",
        "Swagman transposition ACA"
    ]
    groups["Tri-square triples"] := [
        "Tri-square ACA classic",
        "Tri-square ACA period v2",
        "Tri-square classic",
        "Tri-square Delastelle token",
        "Tri-square military variant"
    ]
    groups["Trifid coordinates"] := [
        "Delastelle Trifid 1902 army variant",
        "Delastelle Trifid classic period 5",
        "Trifid cipher period 7",
        "Trifid coordinate stream",
        "Trifid Delastelle",
        "Trifid Delastelle 1901 period 6",
        "Trifid Delastelle 3D",
        "Trifid Delastelle no-period classic",
        "Trifid Delastelle period 5 v3",
        "Trifid Delastelle period 7 v2",
        "Trifid fractionating period 3",
        "Trifid fractionating period 9",
        "Trifid layer token",
        "Trifid numeric fraction",
        "Trifid period 10 Delastelle",
        "Trifid period 5 classic",
        "Trifid raw coords"
    ]
    groups["Two-square pairs"] := [
        "Doppelkasten checkerboard keyed",
        "Doppelkasten German double-box",
        "Doppelkasten German horizontal v3",
        "Doppelkasten German vertical v3",
        "Doppelkasten Wehrmacht field v4",
        "Doppelkasten Wehrmacht horizontal",
        "Doppelkasten Wehrmacht vertical",
        "German Doppelkasten horizontal",
        "German Doppelkasten vertical",
        "Two-square Delastelle",
        "Two-square French army v2",
        "Two-square French diplomatic v3",
        "Two-square French variant",
        "Two-square German army",
        "Two-square German field variant",
        "Two-square horizontal classic",
        "Two-square horizontal Delastelle"
    ]
    groups["Two-square vertical pairs"] := [
        "Two-square vertical classic"
    ]
    groups["Variant Beaufort"] := [
        "Keyed Variant Beaufort",
        "Progressive Variant Beaufort",
        "Variant Beaufort autoclave",
        "Variant Beaufort Fibonacci",
        "Variant Beaufort German classic",
        "Variant Beaufort German style",
        "Variant Beaufort Jacobsthal stream",
        "Variant Beaufort keyed alphabet",
        "Variant Beaufort Lucas stream",
        "Variant Beaufort military key v2",
        "Variant Beaufort Pell stream",
        "Variant Beaufort prime",
        "Variant Beaufort reciprocal field",
        "Variant Beaufort reciprocal v2"
    ]
    groups["VIC checkerboard"] := [
        "Numbers station Slavic groups",
        "Soviet VIC agent style",
        "Soviet VIC pencil-and-paper v6",
        "Straddling checkerboard VIC v4",
        "VIC additive checkerboard v2",
        "VIC agent checkerboard v4",
        "VIC agent checkerboard variant",
        "VIC agent pad groups v2",
        "VIC chain addition classic",
        "VIC chain addition lagged v2",
        "VIC chain addition lagged v4",
        "VIC chain addition toy",
        "VIC chain addition v5",
        "VIC checkerboard classic",
        "VIC checkerboard five-line v5",
        "VIC checkerboard lagged key v6",
        "VIC cipher full classic",
        "VIC cipher pencil-paper v7",
        "VIC lagged Fibonacci addition v2",
        "VIC lagged Fibonacci classic",
        "VIC personal date key v3",
        "VIC personal number key v2",
        "VIC sequential transposition style",
        "VIC sequential transposition v2",
        "VIC sequential transposition v3",
        "VIC sequential transposition v4",
        "VIC straddling checkerboard full",
        "VIC straddling checkerboard v3",
        "VIC transposition final v2",
        "VIC transposition phase token"
    ]
    groups["Vigenere"] := [
        "Autoclave Vigenere",
        "Babbage autokey cipher",
        "Babbage autokey cryptanalysis sample",
        "Babbage autokey sample v2",
        "Babbage progressive key Vigenere",
        "Babbage Vigenere",
        "Chiffre indechiffrable",
        "Confederate Vigenere disk v2",
        "Interrupted key Vigenere",
        "Kasiski keyed Vigenere variant",
        "Kasiski repeated-key cipher",
        "Kasiski repeated-key sample v3",
        "Kasiski repeated-key Vigenere",
        "Kasiski Vigenere",
        "Kasiski Vigenere training cipher v2",
        "Key phrase Vigenere",
        "Nicodemus columnar Vigenere v4",
        "Nicodemus transposition Vigenere v2",
        "Printable Vigenere",
        "Progressive key Vigenere",
        "Reciprocal Vigenere",
        "Slide Vigenere",
        "Vigenere Catalan stream",
        "Vigenere chiffre indechiffrable v2",
        "Vigenere cube stream",
        "Vigenere Fibonacci stream",
        "Vigenere Jacobsthal stream",
        "Vigenere keyed alphabet",
        "Vigenere Lucas stream",
        "Vigenere minus key",
        "Vigenere numerical key",
        "Vigenere Padovan stream",
        "Vigenere Pell stream",
        "Vigenere prime stream",
        "Vigenere prime-gap stream",
        "Vigenere reciprocal alphabet",
        "Vigenere reciprocal table variant",
        "Vigenere repeated key 19th century v2",
        "Vigenere reversed alphabet",
        "Vigenere square 19th-century",
        "Vigenere square stream",
        "Vigenere tableau classic",
        "Vigenere tabula recta diplomatic v3",
        "Vigenere tabula recta Latin v2",
        "Vigenere Tetranacci stream",
        "Vigenere triangular stream"
    ]

    for baseMode, presets in groups {
        if !m.Has(baseMode)
            m[baseMode] := ["Custom"]
        for _, presetName in presets
            AddPresetIfMissing(m[baseMode], presetName)
    }
}

RemoveHiddenPresetEntries(m) {
    global MODE_LIST
    visible := Map()
    for _, mode in MODE_LIST
        visible[mode] := true


deleteKeys := []
    for presetMode, _ in m {
        if !visible.Has(presetMode)
            deleteKeys.Push(presetMode)
    }
    for _, presetMode in deleteKeys
        m.Delete(presetMode)
}

GetPresetsForMode(mode) {
    global PRESETS_BY_MODE
    if PRESETS_BY_MODE.Has(mode)
        return PRESETS_BY_MODE[mode]
    return ["Custom"]
}

RefreshPresetList(selectPreset := "Custom") {
    global presetBox, modeName
    presets := GetPresetsForMode(modeName)
    try presetBox.Delete()
    presetBox.Add(presets)
    presetBox.Choose(IndexOf(presets, selectPreset))
}

SearchChanged(*) {
    global searchBox
    FilterModeList(searchBox.Value)
}

FilterModeList(query := "") {
    global MODE_LIST, displayedModeList, modeBox, modeName
    displayedModeList := []
    rawQuery := Trim(query)
    q := StrLower(rawQuery)
    isCategorySearch := SubStr(q, 1, 1) = "#"
    category := isCategorySearch ? Trim(SubStr(q, 2)) : ""

    for _, item in MODE_LIST {
        if isCategorySearch {
            if ModeMatchesCategory(item, category)
                displayedModeList.Push(item)
        } else if q = "" || InStr(StrLower(item), q) {
            displayedModeList.Push(item)
        }
    }

    if displayedModeList.Length = 0
        displayedModeList.Push("No ciphers found")
    try modeBox.Delete()
    modeBox.Add(displayedModeList)
    if displayedModeList[1] = "No ciphers found" {
        modeBox.Choose(1)
        return
    }
    modeBox.Choose(IndexOf(displayedModeList, modeName))
}

ModeMatchesCategory(mode, category) {
    category := StrLower(Trim(category))
    if category = ""
        return true

    modeLower := StrLower(mode)
    if InStr(modeLower, category)
        return true

    keywords := CategoryKeywords(category)
    if keywords.Length = 0
        return false

    for _, keyword in keywords {
        if keyword != "" && InStr(modeLower, keyword)
            return true
    }
    return false
}

CategoryKeywords(category) {
    category := StrLower(Trim(category))

    if CategoryIs(category, "caesar", "shift", "rot")
        return ["caesar", "rot13", "rot47", "trithemius", "saint-cyr", "st. cyr", "st cyr", "augustus", "shift"]

    if CategoryIs(category, "vigenere", "vig", "polyalphabetic")
        return ["vigenere", "autokey", "autoclave", "bellaso", "chiffre", "running key", "primer", "indec", "kasiski", "progressive key"]

    if CategoryIs(category, "beaufort")
        return ["beaufort"]

    if CategoryIs(category, "gronsfeld")
        return ["gronsfeld"]

    if CategoryIs(category, "quagmire")
        return ["quagmire"]

    if CategoryIs(category, "porta", "portax")
        return ["porta", "portax"]

    if CategoryIs(category, "playfair", "digraph", "polygraphic")
        return ["playfair", "two-square", "two square", "four-square", "four square", "doppelkasten", "slidefair", "digrafid", "tri-square", "trisquare", "foursquare"]

    if CategoryIs(category, "polybius", "checkerboard", "fractionation")
        return ["polybius", "checkerboard", "adfgx", "adfgvx", "nihilist", "bifid", "trifid", "tap", "prison tap", "fractionated", "straddling", "monome", "dinome", "grandpre", "gedefu", "vic"]

    if CategoryIs(category, "transposition", "route")
        return ["transposition", "columnar", "route", "rail", "scytale", "myszkowski", "amsco", "swagman", "cadenus", "caesar box", "boustrophedon", "spiral", "grille", "cardan", "fleissner", "ubchi"]

    if CategoryIs(category, "columnar")
        return ["columnar", "myszkowski", "amsco", "cadenus", "swagman", "ubchi", "transposition"]

    if CategoryIs(category, "rail")
        return ["rail", "redefence", "zigzag"]

    if CategoryIs(category, "grille")
        return ["grille", "cardan", "fleissner"]

    if CategoryIs(category, "rotor", "machine", "machines")
        return ["enigma", "typex", "sigaba", "hagelin", "m-209", "m209", "lorenz", "siemens", "purple", "hebern", "kryha", "fialka", "nema", "kl-7", "kw-26", "kw-7", "rockex", "sigtot", "rotor", "machine"]

    if CategoryIs(category, "enigma")
        return ["enigma"]

    if CategoryIs(category, "stream", "xor")
        return ["stream", "rc4", "arcfour", "chacha", "salsa", "xor", "vernam", "lfsr", "xorshift", "blum", "lcg", "otp", "one-time", "diana", "solitaire", "pontifex"]

    if CategoryIs(category, "otp", "onetime", "one-time")
        return ["otp", "one-time", "vernam", "diana", "sigtot", "rockex"]

    if CategoryIs(category, "substitution", "sub")
        return ["substitution", "atbash", "affine", "keyed alphabet", "aristocrat", "patristocrat", "homophonic", "chaocipher", "kamasutra", "alphabet", "reciprocal", "keyword"]

    if CategoryIs(category, "affine")
        return ["affine", "multiplicative", "decimation"]

    if CategoryIs(category, "homophonic")
        return ["homophonic", "zodiac", "great cipher"]

    if CategoryIs(category, "book", "codebook", "code")
        return ["book", "codebook", "nomenclator", "diplomatic", "cable", "telegraph code", "poem", "commercial code", "beale", "zimmermann", "mary", "babington", "great cipher", "rossignol", "numbers station", "jn-25", "jn25"]

    if CategoryIs(category, "nomenclator")
        return ["nomenclator", "great cipher", "rossignol", "mary", "babington"]

    if CategoryIs(category, "morse")
        return ["morse", "pollux", "morbit"]

    if CategoryIs(category, "bacon", "baconian", "biliteral")
        return ["bacon", "baconian", "biliteral"]

    if CategoryIs(category, "keyboard")
        return ["keyboard", "qwerty", "dvorak", "colemak", "azerty", "qwertz"]

    if CategoryIs(category, "phone", "t9")
        return ["phone", "t9", "multitap", "vanity"]

    if CategoryIs(category, "phonetic")
        return ["nato", "apco", "lapd", "raf", "phonetic"]

    if CategoryIs(category, "telegraph", "teleprinter")
        return ["baudot", "murray", "ita1", "ita2", "rtty", "teleprinter", "telegraph", "chappe", "optical", "signals", "flag", "maritime", "signal"]

    if CategoryIs(category, "encoding", "encode", "base")
        return ["base", "ascii", "unicode", "utf", "binary", "hex", "octal", "decimal", "url", "html", "xml", "mime", "quoted", "pem", "pgp", "yenc", "z85", "bech32", "punycode", "netstring", "bencode", "data uri", "messagepack", "intel", "s-record"]

    if CategoryIs(category, "ascii")
        return ["ascii", "printable"]

    if CategoryIs(category, "unicode")
        return ["unicode", "utf", "xml", "html entity", "entity"]

    if CategoryIs(category, "numeric", "number", "numbers")
        return ["a1z26", "numeric", "number", "prime", "fibonacci", "lucas", "pell", "jacobsthal", "padovan", "triangular", "squared", "cubed", "factorial", "roman", "gematria", "isopsephy", "godel", "cantor", "catalan", "bell", "zeckendorf", "resistor"]

    if CategoryIs(category, "checksum", "hash")
        return ["crc", "adler", "fletcher", "luhn", "damm", "verhoeff", "check", "syndrome", "hash", "md5", "sha"]

    if CategoryIs(category, "symbol", "symbols", "visual")
        return ["symbol", "runes", "ogham", "futhark", "cyrillic", "greek", "hebrew", "armenian", "georgian", "katakana", "hiragana", "hangul", "braille", "emoji", "wingdings", "aurebesh", "theban", "dancing men", "zodiac", "pigpen", "rosicrucian", "templar", "masonic", "moon", "tengwar", "cirth", "flag", "semaphore", "geometric", "box drawing", "mathematical", "fraktur", "script", "small caps", "superscript", "subscript", "zalgo", "mirror", "upside"]

    if CategoryIs(category, "ancient")
        return ["aeneas", "scytale", "polybius", "temurah", "albam", "atbah", "mlecchita", "arthashastra", "runestone", "rök", "greek torch"]

    if CategoryIs(category, "military", "army", "field")
        return ["military", "army", "field", "tactical", "batco", "slidex", "dryad", "soe", "nato", "acp", "vic", "enigma", "adfgx", "adfgvx", "one-time pad", "vernam", "m-209", "typex", "sigaba"]

    if CategoryIs(category, "diplomatic")
        return ["diplomatic", "nomenclator", "codebook", "zimmermann", "purple", "red", "orange", "vatican", "papal", "venetian"]

    if CategoryIs(category, "stego", "steganography")
        return ["stego", "acrostic", "null", "invisible", "zero width", "whitespace", "snow", "italic", "cover", "headline"]

    if CategoryIs(category, "barcode")
        return ["barcode", "qr", "code39", "code128", "pdf417", "datamatrix", "aztec", "upc", "ean", "isbn", "codabar", "code93", "msi", "postnet", "planet", "royal mail", "kix", "micr", "gs1", "pharmacode"]

    return [category]
}

CategoryIs(category, aliases*) {
    for _, alias in aliases {
        if category = alias
            return true
    }
    return false
}

ModeChanged(*) {
    global modeBox, displayedModeList, modeName
    selectedMode := SelectedFrom(modeBox, displayedModeList)
    if selectedMode = "No ciphers found"
        return
    modeName := selectedMode
    RefreshPresetList("Custom")
    UpdateModePanel()
    ResetState()
    UpdateStatus()
}

PresetChanged(*) {
    ; Selection alone does not change settings. Click Apply preset.
}

ApplyPresetClicked(*) {
    global presetBox, modeName
    presets := GetPresetsForMode(modeName)
    preset := SelectedFrom(presetBox, presets)
    ApplyPreset(preset)
}

ApplyPreset(preset) {
    global shiftEdit, keyEdit, affineAEdit, affineBEdit, substitutionEdit, plugboardEdit
    global quagPlainEdit, quagCipherEdit, quagIndicatorEdit, quagPositionBox, ALPHABET
    if preset = "Custom"
        return

    if InStr(preset, " — random key") {
        keyEdit.Value := RandomLetters(Random(5, 12))
        return FinishPresetApply(preset)
    }

    if InStr(preset, "Quagmire") {
        ApplyQuagmirePreset(preset)
        return FinishPresetApply(preset)
    }

    if InStr(preset, "random preset") || InStr(preset, "random full machine") {
        if InStr(preset, "M3") {
            ApplyRandomEnigmaPreset("Enigma M3")
            return FinishPresetApply(preset)
        }
        if InStr(preset, "M4") {
            ApplyRandomEnigmaPreset("Enigma M4")
            return FinishPresetApply(preset)
        }
    }

    if preset = "M3 — random plugboard" {
        ApplySettingsCore(false)
        plugboardEdit.Value := RandomPlugboardPairs(Random(5, 10))
        return FinishPresetApply(preset)
    }
    if preset = "M4 — random plugboard" {
        ApplySettingsCore(false)
        plugboardEdit.Value := RandomPlugboardPairs(Random(6, 10))
        return FinishPresetApply(preset)
    }

    if ApplyCollapsedSettingPreset(preset)
        return FinishPresetApply(preset)

    switch preset {
        case "M3 — Army default I-II-III B AAA":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "AAA", "AAA", "AB CD EF")
        case "M3 — no plugboard AAA":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "AAA", "AAA", "")
        case "M3 — no plugboard ZZZ":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "ZZZ", "AAA", "")
        case "M3 — strong plugboard DOG":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "DOG", "AAA", "PO ML KI JU HY GT FR DE SW QA")
        case "M3 — training AAB":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "AAB", "AAA", "AV BS CG DL FU HZ IN KM OW RX")
        case "M3 — message key CAT":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "CAT", "AAA", "AZ BY CX DW EV FU GT HS IR JQ")
        case "M3 — midnight MCK":
            SetEnigmaPreset("Enigma M3", "Beta", "II", "IV", "V", "B", "MCK", "AAA", "AQ BJ CL DK ER FS GT HY IU OW")
        case "M3 — Bletchley style":
            SetEnigmaPreset("Enigma M3", "Beta", "III", "I", "II", "B", "BLY", "AAA", "AM FI NV PS TU WZ")
        case "M3 — naval style I-II-V":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "V", "C", "SEA", "AAA", "AN EZ HK IJ LR MQ OT PV SW UX")
        case "M3 — rotor IV-V-I":
            SetEnigmaPreset("Enigma M3", "Beta", "IV", "V", "I", "B", "RAT", "AAA", "AF BG CH DI EJ KL MN OP QS TX")
        case "M3 — rotor V-III-II":
            SetEnigmaPreset("Enigma M3", "Beta", "V", "III", "II", "C", "FOX", "AAA", "AP BO CN DM EL FK GI HJ QZ RX")
        case "M3 — turnover test VEV":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "VEV", "AAA", "")
        case "M3 — rings BCD":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "AAA", "BCD", "AB CD EF")
        case "M3 — rings MCK":
            SetEnigmaPreset("Enigma M3", "Beta", "III", "II", "I", "B", "MCK", "MCK", "PO ML KI JU HY GT FR DE SW QA")
        case "M3 — alphabet pairs":
            SetEnigmaPreset("Enigma M3", "Beta", "I", "II", "III", "B", "QWE", "AAA", "AZ BY CX DW EV FU GT HS IR JQ KP LO MN")

        case "M4 — Beta I-II-III B Thin AAAA":
            SetEnigmaPreset("Enigma M4", "Beta", "I", "II", "III", "B Thin", "AAAA", "AAAA", "AB CD EF")
        case "M4 — Gamma I-II-III C Thin AAAA":
            SetEnigmaPreset("Enigma M4", "Gamma", "I", "II", "III", "C Thin", "AAAA", "AAAA", "AB CD EF")
        case "M4 — no plugboard ZZZZ":
            SetEnigmaPreset("Enigma M4", "Beta", "I", "II", "III", "B Thin", "ZZZZ", "AAAA", "")
        case "M4 — naval U-boat 1":
            SetEnigmaPreset("Enigma M4", "Beta", "II", "IV", "V", "B Thin", "UBOT", "AAAA", "AN EZ HK IJ LR MQ OT PV SW UX")
        case "M4 — naval U-boat 2":
            SetEnigmaPreset("Enigma M4", "Gamma", "VIII", "VI", "III", "C Thin", "BOAT", "AAAA", "AV BS CG DL FU HZ IN KM OW RX")
        case "M4 — Triton style":
            SetEnigmaPreset("Enigma M4", "Beta", "VIII", "VI", "V", "B Thin", "TRIT", "AAAA", "AQ BJ CL DK ER FS GT HY IU OW")
        case "M4 — Beta IV-V-II":
            SetEnigmaPreset("Enigma M4", "Beta", "IV", "V", "II", "B Thin", "BETA", "AAAA", "PO ML KI JU HY GT FR DE SW QA")
        case "M4 — Gamma VIII-VI-III":
            SetEnigmaPreset("Enigma M4", "Gamma", "VIII", "VI", "III", "C Thin", "GAMM", "AAAA", "AF BG CH DI EJ KL MN OP QS TX")
        case "M4 — message key WAVE":
            SetEnigmaPreset("Enigma M4", "Beta", "VII", "II", "IV", "B Thin", "WAVE", "AAAA", "AM FI NV PS TU WZ")
        case "M4 — message key BOAT":
            SetEnigmaPreset("Enigma M4", "Gamma", "VI", "III", "I", "C Thin", "BOAT", "AAAA", "AP BO CN DM EL FK GI HJ QZ RX")
        case "M4 — rings AAAA":
            SetEnigmaPreset("Enigma M4", "Beta", "I", "II", "III", "B Thin", "AAAA", "AAAA", "AB CD EF")
        case "M4 — rings BETA":
            SetEnigmaPreset("Enigma M4", "Beta", "I", "II", "III", "B Thin", "AAAA", "BETA", "AB CD EF")
        case "M4 — rings MARS":
            SetEnigmaPreset("Enigma M4", "Gamma", "VIII", "VI", "III", "C Thin", "MARS", "MARS", "AN EZ HK IJ LR MQ OT PV SW UX")
        case "M4 — thin Beta strong plugboard":
            SetEnigmaPreset("Enigma M4", "Beta", "VIII", "V", "I", "B Thin", "KEYS", "AAAA", "PO ML KI JU HY GT FR DE SW QA")
        case "M4 — thin Gamma strong plugboard":
            SetEnigmaPreset("Enigma M4", "Gamma", "VII", "IV", "II", "C Thin", "LOCK", "AAAA", "AZ BY CX DW EV FU GT HS IR JQ")

        case "Caesar +1":
            shiftEdit.Value := "1"
        case "Caesar +2":
            shiftEdit.Value := "2"
        case "Caesar +3":
            shiftEdit.Value := "3"
        case "Caesar +5":
            shiftEdit.Value := "5"
        case "Caesar +7":
            shiftEdit.Value := "7"
        case "Caesar +13":
            shiftEdit.Value := "13"
        case "Caesar -1":
            shiftEdit.Value := "-1"
        case "Caesar -3":
            shiftEdit.Value := "-3"
        case "Caesar -5":
            shiftEdit.Value := "-5"
        case "Caesar +19":
            shiftEdit.Value := "19"
        case "Caesar -19":
            shiftEdit.Value := "-19"
        case "Caesar random", "Progressive Caesar random start", "Trithemius random start":
            shiftEdit.Value := Random(-25, 25)
        case "Progressive Caesar start 0", "Trithemius start 0":
            shiftEdit.Value := "0"
        case "Progressive Caesar start 3":
            shiftEdit.Value := "3"
        case "Trithemius start 1":
            shiftEdit.Value := "1"

        case "Vigenere — LEMON":
            keyEdit.Value := "LEMON"
        case "Vigenere — DRAGON":
            keyEdit.Value := "DRAGON"
        case "Vigenere — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Vigenere — SHADOW":
            keyEdit.Value := "SHADOW"
        case "Vigenere — ORANGE":
            keyEdit.Value := "ORANGE"
        case "Vigenere — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Vigenere — ENIGMA":
            keyEdit.Value := "ENIGMA"
        case "Vigenere — SECRET":
            keyEdit.Value := "SECRET"
        case "Autokey — QUEENLY":
            keyEdit.Value := "QUEENLY"
        case "Autokey — CIPHER", "Keyword — CIPHER", "Beaufort — CIPHER", "Porta — CIPHER", "Variant Beaufort — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Autokey — DRAGON", "Keyword — DRAGON", "Porta — DRAGON":
            keyEdit.Value := "DRAGON"
        case "Autokey — MONARCHY", "Keyword — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Autokey — SECRET", "Keyword — SECRET", "Porta — SECRET":
            keyEdit.Value := "SECRET"
        case "Beaufort — FORT", "Variant Beaufort — FORT":
            keyEdit.Value := "FORT"
        case "Beaufort — KEY", "Porta — KEY", "Variant Beaufort — KEY":
            keyEdit.Value := "KEY"
        case "Beaufort — LEMON":
            keyEdit.Value := "LEMON"
        case "Beaufort — ENIGMA", "Keyword — ENIGMA":
            keyEdit.Value := "ENIGMA"
        case "Porta — PORTA":
            keyEdit.Value := "PORTA"
        case "Keyword — QWERTY":
            keyEdit.Value := "QWERTY"
        case "Keyword — ZEBRAS":
            keyEdit.Value := "ZEBRAS"
        case "Vigenere — random key", "Autokey — random key", "Beaufort — random key", "Variant Beaufort — random key", "Porta — random key", "Keyword — random key":
            keyEdit.Value := RandomLetters(Random(4, 10))
        case "Running key — THEQUICKBROWNFOX":
            keyEdit.Value := "THEQUICKBROWNFOX"
        case "Running key — CRYPTOGRAPHY":
            keyEdit.Value := "CRYPTOGRAPHY"
        case "Running key — random long key":
            keyEdit.Value := RandomLetters(Random(16, 32))
        case "Gronsfeld — 31415":
            keyEdit.Value := "31415"
        case "Gronsfeld — 27182":
            keyEdit.Value := "27182"
        case "Gronsfeld — 12345":
            keyEdit.Value := "12345"
        case "Gronsfeld — random digits":
            keyEdit.Value := RandomDigits(Random(4, 10))

        case "Affine 1,13":
            affineAEdit.Value := "1"
            affineBEdit.Value := "13"
        case "Affine 3,7":
            affineAEdit.Value := "3"
            affineBEdit.Value := "7"
        case "Affine 5,8":
            affineAEdit.Value := "5"
            affineBEdit.Value := "8"
        case "Affine 7,3":
            affineAEdit.Value := "7"
            affineBEdit.Value := "3"
        case "Affine 11,6":
            affineAEdit.Value := "11"
            affineBEdit.Value := "6"
        case "Affine 17,20":
            affineAEdit.Value := "17"
            affineBEdit.Value := "20"
        case "Affine 25,25":
            affineAEdit.Value := "25"
            affineBEdit.Value := "25"
        case "Affine random":
            validA := [1,3,5,7,9,11,15,17,19,21,23,25]
            affineAEdit.Value := validA[Random(1, validA.Length)]
            affineBEdit.Value := Random(0, 25)

        case "Keyed alphabet Caesar +1":
            keyEdit.Value := "CIPHER"
            shiftEdit.Value := "1"
        case "Keyed alphabet Caesar +3":
            keyEdit.Value := "CIPHER"
            shiftEdit.Value := "3"
        case "Keyed alphabet Caesar +5":
            keyEdit.Value := "CIPHER"
            shiftEdit.Value := "5"
        case "Keyed alphabet Caesar +13":
            keyEdit.Value := "CIPHER"
            shiftEdit.Value := "13"
        case "Keyed alphabet Caesar random":
            keyEdit.Value := RandomLetters(Random(5, 12))
            shiftEdit.Value := Random(-25, 25)

        case "XOR hex — KEY", "XOR binary — KEY":
            keyEdit.Value := "KEY"
        case "XOR hex — SECRET", "XOR binary — SECRET":
            keyEdit.Value := "SECRET"
        case "XOR hex — random key", "XOR binary — random key":
            keyEdit.Value := RandomLetters(Random(4, 12))
        case "Condi — CIPHER", "Playfair — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Condi — KEYWORD":
            keyEdit.Value := "KEYWORD"
        case "Playfair — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Playfair — SECRET":
            keyEdit.Value := "SECRET"
        case "Condi — random key", "Playfair — random key":
            keyEdit.Value := RandomLetters(Random(5, 10))
        case "Bifid — CIPHER", "Two-square — CIPHER", "Four-square — CIPHER", "Nihilist — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Bifid — MONARCHY", "Two-square — MONARCHY", "Four-square — MONARCHY", "Nihilist — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Bifid — SECRET", "Nihilist — SECRET":
            keyEdit.Value := "SECRET"
        case "Bifid — random key", "Two-square — random key", "Four-square — random key", "Nihilist — random key":
            keyEdit.Value := RandomLetters(Random(5, 10))
        case "Keyboard Caesar +1", "Vowel Caesar +1", "Consonant Caesar +1":
            shiftEdit.Value := "1"
        case "Keyboard Caesar +3", "Alternating Caesar +3":
            shiftEdit.Value := "3"
        case "Vowel Caesar +2":
            shiftEdit.Value := "2"
        case "Consonant Caesar +5":
            shiftEdit.Value := "5"
        case "Alternating Caesar +7":
            shiftEdit.Value := "7"
        case "Keyboard Caesar random", "Vowel Caesar random", "Consonant Caesar random", "Alternating Caesar random":
            shiftEdit.Value := Random(-25, 25)

        case "Progressive Vigenere — LEMON":
            keyEdit.Value := "LEMON"
        case "Progressive Vigenere — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Progressive Vigenere — random key":
            keyEdit.Value := RandomLetters(Random(5, 12))
        case "Quagmire I — CIPHER", "Quagmire II — CIPHER", "Quagmire III — CIPHER", "Quagmire IV — CIPHER", "Alberti — CIPHER", "Bellaso — CIPHER", "Autokey Beaufort — CIPHER", "Progressive Porta — CIPHER", "Keyed Atbash — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Quagmire I — MONARCHY", "Quagmire II — MONARCHY", "Quagmire III — MONARCHY", "Quagmire IV — MONARCHY", "Alberti — MONARCHY", "Keyed Atbash — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Bellaso — LEMON":
            keyEdit.Value := "LEMON"
        case "Autokey Beaufort — FORT":
            keyEdit.Value := "FORT"
        case "Progressive Porta — PORTA":
            keyEdit.Value := "PORTA"
        case "Gronsfeld progressive — 31415":
            keyEdit.Value := "31415"
        case "Gronsfeld progressive — 27182":
            keyEdit.Value := "27182"
        case "Gronsfeld progressive — random digits":
            keyEdit.Value := RandomDigits(Random(4, 10))
        case "Quagmire I — random key", "Quagmire II — random key", "Quagmire III — random key", "Quagmire IV — random key", "Alberti — random key", "Bellaso — random key", "Autokey Beaufort — random key", "Progressive Porta — random key", "Keyed Atbash — random key":
            keyEdit.Value := RandomLetters(Random(5, 12))
        case "Diana — SECRET":
            keyEdit.Value := "SECRET"
        case "Diana — LEMON":
            keyEdit.Value := "LEMON"
        case "Diana — random key":
            keyEdit.Value := RandomLetters(Random(8, 16))

        case "Keyed Polybius — CIPHER", "Keyed ADFGX — CIPHER", "Keyed ADFGVX — CIPHER", "Fractionated Morse — CIPHER", "Kamasutra — CIPHER", "Phillips — CIPHER", "Slidefair — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Keyed Polybius — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Keyed ADFGX — PHQG":
            keyEdit.Value := "PHQGIUMEAYLNOFDXKRCVSTZWB"
        case "Keyed ADFGVX — NUMBERS":
            keyEdit.Value := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        case "Morbit — 123456789":
            keyEdit.Value := "123456789"
        case "Morbit — random digits":
            keyEdit.Value := RandomDigitPermutation(9)
        case "Fractionated Morse — SECRET":
            keyEdit.Value := "SECRET"
        case "Kamasutra — alphabet halves":
            keyEdit.Value := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        case "Phillips — PHILLIPS":
            keyEdit.Value := "PHILLIPS"
        case "Slidefair — SLIDE":
            keyEdit.Value := "SLIDE"
        case "Keyed Polybius — random key", "Keyed ADFGX — random key", "Keyed ADFGVX — random key", "Fractionated Morse — random key", "Kamasutra — random key", "Phillips — random key", "Slidefair — random key":
            keyEdit.Value := RandomLetters(Random(5, 12))

        case "Rail fence — rails 3":
            shiftEdit.Value := "3"
        case "Rail fence — rails 4":
            shiftEdit.Value := "4"
        case "Rail fence — random rails":
            shiftEdit.Value := Random(2, 6)
        case "Scytale — width 4":
            shiftEdit.Value := "4"
        case "Scytale — width 5":
            shiftEdit.Value := "5"
        case "Scytale — random width":
            shiftEdit.Value := Random(3, 8)
        case "Columnar — ZEBRAS", "Double columnar — ZEBRAS":
            keyEdit.Value := "ZEBRAS"
        case "Columnar — CARGO", "Double columnar — CARGO":
            keyEdit.Value := "CARGO"
        case "Columnar — SECRET":
            keyEdit.Value := "SECRET"
        case "Columnar — random key", "Double columnar — random key":
            keyEdit.Value := RandomLetters(Random(5, 10))
        case "Route cipher — 3x3 spiral":
            shiftEdit.Value := "3"
        case "Route cipher — 4x4 spiral":
            shiftEdit.Value := "4"
        case "Myszkowski — BALLOON":
            keyEdit.Value := "BALLOON"
        case "Myszkowski — MISSISSIPPI":
            keyEdit.Value := "MISSISSIPPI"
        case "Myszkowski — random key":
            keyEdit.Value := RandomLetters(Random(6, 11))
        case "Jefferson — CIPHER", "M-94 — CIPHER", "Bazeries — CIPHER", "VIC checkerboard — CIPHER", "Bifid full — CIPHER", "Trifid full — CIPHER", "Nihilist numeric — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Jefferson — PRESIDENT":
            keyEdit.Value := "PRESIDENT"
        case "M-94 — ARMY":
            keyEdit.Value := "ARMY"
        case "Bazeries — FRANCE":
            keyEdit.Value := "FRANCE"
        case "Jefferson — random key", "M-94 — random key", "Bazeries — random key", "VIC checkerboard — random key", "Bifid full — random key", "Trifid full — random key", "Nihilist numeric — random key":
            keyEdit.Value := RandomLetters(Random(5, 14))
        case "M-209 — default pins":
            keyEdit.Value := "HAGELIN"
        case "M-209 — random start":
            keyEdit.Value := RandomLetters(Random(6, 12))
            shiftEdit.Value := Random(0, 25)
        case "VIC checkerboard — ETAOIN":
            keyEdit.Value := "ETAOINSHRDLU"
        case "OTP — LEMON", "Vernam — LEMON":
            keyEdit.Value := "LEMON"
        case "OTP — SECRET", "Vernam — SECRET", "RC4 — SECRET", "Solitaire — SECRET":
            keyEdit.Value := "SECRET"
        case "OTP — random pad":
            keyEdit.Value := RandomLetters(Random(20, 40))
        case "Vernam — random key", "RC4 — random key", "Solitaire — random key":
            keyEdit.Value := RandomLetters(Random(6, 16))
        case "RC4 — KEY":
            keyEdit.Value := "KEY"
        case "Solitaire — CRYPTO":
            keyEdit.Value := "CRYPTO"
        case "Bifid full — MONARCHY", "Nihilist numeric — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Trifid full — TRIFID":
            keyEdit.Value := "TRIFID"
        case "Book cipher — NATO":
            keyEdit.Value := "ALPHA BRAVO CHARLIE DELTA ECHO FOXTROT GOLF HOTEL INDIA JULIET KILO LIMA MIKE NOVEMBER OSCAR PAPA QUEBEC ROMEO SIERRA TANGO UNIFORM VICTOR WHISKEY XRAY YANKEE ZULU"
        case "Book cipher — POE":
            keyEdit.Value := "ONCE UPON A MIDNIGHT DREARY WHILE I PONDERED WEAK AND WEARY"
        case "Book cipher — random book key":
            keyEdit.Value := RandomLetters(Random(12, 24))

        case "Ragbaby — RAGBABY":
            keyEdit.Value := "RAGBABY"
        case "Ragbaby — CIPHER", "Nicodemus — CIPHER", "Clave — CIPHER", "Gromark — CIPHER", "Seriated Playfair — KEYWORD", "Playfair 6x6 — KEYWORD", "Bifid 6x6 — KEYWORD":
            keyEdit.Value := InStr(preset, "KEYWORD") ? "KEYWORD" : "CIPHER"
        case "Nicodemus — NICODEMUS":
            keyEdit.Value := "NICODEMUS"
        case "Clave — CLAVE":
            keyEdit.Value := "CLAVE"
        case "Gromark — primer 12345", "Swagman — 3142":
            keyEdit.Value := InStr(preset, "Swagman") ? "3142" : "12345"
        case "Gromark — random primer", "Swagman — random digits":
            keyEdit.Value := RandomDigits(Random(4, 8))
        case "Seriated Playfair — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Playfair 6x6 — NUMBERS":
            keyEdit.Value := "NUMBERS"
        case "Two-square vertical — EXAMPLE", "Two-square 6x6 — EXAMPLE", "Four-square 6x6 — EXAMPLE":
            keyEdit.Value := "EXAMPLE"
        case "Two-square vertical — CIPHER", "Tri-square — CIPHER", "Two-square 6x6 — CIPHER", "Four-square 6x6 — CIPHER", "Cadenus — CIPHER", "AMSCO — CIPHER", "Disrupted — CIPHER", "Incomplete columnar — CIPHER", "Complete columnar — CIPHER", "Alternating columnar — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Tri-square — ALPHA":
            keyEdit.Value := "ALPHA"
        case "Hill 3x3 — classic":
            keyEdit.Value := "GYBNQKURP"
        case "Hill 3x3 — random start":
            keyEdit.Value := RandomLetters(9)
        case "Cadenus — CADENUS":
            keyEdit.Value := "CADENUS"
        case "AMSCO — ZEBRAS", "Incomplete columnar — ZEBRAS", "Complete columnar — ZEBRAS", "Alternating columnar — ZEBRAS":
            keyEdit.Value := "ZEBRAS"
        case "Swagman — 2413":
            keyEdit.Value := "2413"
        case "Bazeries — BAZERIES 31415":
            keyEdit.Value := "BAZERIES"
            shiftEdit.Value := "31415"
        case "Bazeries — CIPHER 27182":
            keyEdit.Value := "CIPHER"
            shiftEdit.Value := "27182"
        case "Bazeries — random":
            keyEdit.Value := RandomLetters(Random(6, 10))
            shiftEdit.Value := RandomDigits(5)
        case "Disrupted — DISRUPT":
            keyEdit.Value := "DISRUPT"
        case "ADFGVX escaped — KEYW0RD":
            keyEdit.Value := "KEYW0RD"
        case "ADFGVX escaped — random key":
            keyEdit.Value := RandomLetters(Random(5, 10))
        case "Boustrophedon — 4x4", "Spiral inward — 4x4", "Spiral outward — 4x4", "Rotating square — 90":
            shiftEdit.Value := "4"
        case "Boustrophedon — 5x5", "Spiral inward — 5x5", "Spiral outward — 5x5":
            shiftEdit.Value := "5"
        case "Rotating square — 180":
            shiftEdit.Value := "2"
        case "Rotating square — random":
            shiftEdit.Value := Random(1, 3)
        case "Reading route — columns":
            keyEdit.Value := "COLUMN"
        case "Reading route — boustrophedon":
            keyEdit.Value := "SNAKE"
        case "Ragbaby — random key", "Nicodemus — random key", "Clave — random key", "Seriated Playfair — random key", "Playfair 6x6 — random key", "Two-square vertical — random key", "Tri-square — random key", "Two-square 6x6 — random key", "Four-square 6x6 — random key", "Bifid 6x6 — random key", "Cadenus — random key", "AMSCO — random key", "Disrupted — random key", "Incomplete columnar — random key", "Complete columnar — random key", "Alternating columnar — random key":
            keyEdit.Value := RandomLetters(Random(5, 12))


        case "Custom alphabet — QWERTY +3":
            keyEdit.Value := "QWERTYUIOPASDFGHJKLZXCVBNM", shiftEdit.Value := 3
        case "Custom alphabet — random +3":
            keyEdit.Value := RandomSubstitutionAlphabet(), shiftEdit.Value := 3
        case "Della Porta — CIPHER":
            keyEdit.Value := "CIPHER", shiftEdit.Value := 0
        case "Della Porta — MONARCHY":
            keyEdit.Value := "MONARCHY", shiftEdit.Value := 3
        case "Della Porta — random key":
            keyEdit.Value := RandomKey(Random(6, 10)), shiftEdit.Value := Random(0, 25)
        case "Lorenz — LORENZ":
            keyEdit.Value := "LORENZ"
        case "Lorenz — SECRET":
            keyEdit.Value := "SECRET"
        case "Lorenz — random seed":
            keyEdit.Value := RandomKey(Random(6, 12))
        case "Hagelin — HAGELIN":
            keyEdit.Value := "HAGELIN"
        case "Hagelin — SECRET":
            keyEdit.Value := "SECRET"
        case "Hagelin — random seed":
            keyEdit.Value := RandomKey(Random(6, 12))
        case "Redefence — rails 3":
            shiftEdit.Value := 3
        case "Redefence — rails 4":
            shiftEdit.Value := 4
        case "Redefence — random rails":
            shiftEdit.Value := Random(2, 8)
        case "Playfair Q omitted — KEYWORD":
            keyEdit.Value := "KEYWORD"
        case "Playfair Q omitted — MONARCHY":
            keyEdit.Value := "MONARCHY"
        case "Double Playfair — ALPHA/OMEGA", "Twin Bifid — ALPHA/OMEGA":
            keyEdit.Value := "ALPHA OMEGA"
        case "Double Playfair — CIPHER", "Twin Bifid — CIPHER", "Polybius columnar — CIPHER":
            keyEdit.Value := "CIPHER"
        case "Polybius columnar — ZEBRAS":
            keyEdit.Value := "ZEBRAS"
        case "Playfair Q omitted — random key", "Double Playfair — random key", "Twin Bifid — random key", "Polybius columnar — random key":
            keyEdit.Value := RandomKey(Random(6, 10))
        case "Bacon biliteral — AB":
            keyEdit.Value := "AB"
        case "Bacon biliteral — 01":
            keyEdit.Value := "01"
        case "Bacon biliteral — dot dash":
            keyEdit.Value := ".-"
        case "Acrostic cover — COVER":
            keyEdit.Value := "COVER"
        case "Acrostic cover — random tail":
            keyEdit.Value := RandomKey(Random(4, 8))

        case "Keyed Caesar — CIPHER +3":
            keyEdit.Value := "CIPHER", shiftEdit.Value := 3
        case "Keyed Caesar — MONARCHY +5":
            keyEdit.Value := "MONARCHY", shiftEdit.Value := 5
        case "Keyed Caesar — random key", "Keyed progressive — random key", "Interrupted key — random key", "Progressive key — random key", "Variant Beaufort autokey — random key", "Progressive Beaufort — random key", "Progressive Variant Beaufort — random key", "Porta autokey — random key", "Polybius 0 keyed — random key", "Polybius letters — random key", "Fractionated Polybius — random key":
            keyEdit.Value := RandomKey(Random(6, 12)), shiftEdit.Value := Random(1, 9)
        case "Keyed progressive — CIPHER", "Interrupted key — CIPHER", "Progressive key — CIPHER", "Variant Beaufort autokey — CIPHER", "Progressive Beaufort — CIPHER", "Progressive Variant Beaufort — CIPHER", "Porta autokey — CIPHER", "Polybius 0 keyed — CIPHER", "Polybius letters — CIPHER", "Fractionated Polybius — CIPHER":
            keyEdit.Value := "CIPHER", shiftEdit.Value := 3
        case "Keyed progressive — MONARCHY", "Polybius 0 keyed — MONARCHY", "Polybius letters — MONARCHY", "Fractionated Polybius — MONARCHY":
            keyEdit.Value := "MONARCHY", shiftEdit.Value := 3
        case "Interrupted key — SECRET":
            keyEdit.Value := "SECRET", shiftEdit.Value := 5
        case "Progressive key — LEMON":
            keyEdit.Value := "LEMON", shiftEdit.Value := 1
        case "Variant Beaufort autokey — FORT", "Progressive Beaufort — FORT", "Progressive Variant Beaufort — FORT":
            keyEdit.Value := "FORT", shiftEdit.Value := 1
        case "Running book — THEQUICKBROWNFOX":
            keyEdit.Value := "THEQUICKBROWNFOXJUMPSOVERTHELAZYDOG"
        case "Running book — CRYPTOGRAPHY":
            keyEdit.Value := "CRYPTOGRAPHYISAPRACTICEOFSECUREWRITING"
        case "Running book — random long key":
            keyEdit.Value := RandomKey(Random(24, 48))
        case "Porta autokey — PORTA":
            keyEdit.Value := "PORTA"
        case "Grandpre — CRYPTOGRAPHY":
            keyEdit.Value := "CRYPTOGRAPHYALPHABETGRID"
        case "Grandpre — MONARCHY":
            keyEdit.Value := "MONARCHYREPUBLICCIPHERGRID"
        case "Grandpre — random grid":
            keyEdit.Value := RandomKey(Random(40, 70))

        case "Random substitution — random 1", "Random substitution — random 2", "Random substitution — random 3", "Random substitution — random now":
            substitutionEdit.Value := RandomAlphabet()
        case "Random substitution — QWERTY fixed":
            substitutionEdit.Value := "QWERTYUIOPASDFGHJKLZXCVBNM"
        case "Random substitution — reverse fixed":
            substitutionEdit.Value := "ZYXWVUTSRQPONMLKJIHGFEDCBA"
    }

    return FinishPresetApply(preset)
}


ApplyCollapsedSettingPreset(preset) {
    global shiftEdit, keyEdit, affineAEdit, affineBEdit, substitutionEdit
    did := false

    if InStr(preset, "Enigma M4") || InStr(preset, "Triton") || InStr(preset, "U-boat") || InStr(preset, "Shark") {
        ApplyRandomEnigmaPreset("Enigma M4")
        did := true
    } else if InStr(preset, "Enigma M3") || InStr(preset, "Enigma I") || InStr(preset, "Wehrmacht") || InStr(preset, "Heer") || InStr(preset, "Luftwaffe") {
        ApplyRandomEnigmaPreset("Enigma M3")
        did := true
    }

    if RegExMatch(preset, "i)(?:\+|plus\s*)(\d+)", &plusMatch) {
        shiftEdit.Value := plusMatch[1]
        did := true
    } else if RegExMatch(preset, "i)(?:-|minus\s+)(\d+)", &minusMatch) {
        shiftEdit.Value := "-" . minusMatch[1]
        did := true
    } else if RegExMatch(preset, "i)(?:period|rail|rails|width|offset|start|row|rows)\D*(\d+)", &numMatch) {
        shiftEdit.Value := numMatch[1]
        did := true
    } else if RegExMatch(preset, "i)(\d+)x\d+", &gridMatch) {
        shiftEdit.Value := gridMatch[1]
        did := true
    }

    if InStr(preset, "random key") || InStr(preset, "random pad") || InStr(preset, "random primer") {
        keyEdit.Value := RandomLetters(Random(5, 14))
        did := true
    }

    keyWords := ["CIPHER", "MONARCHY", "SECRET", "LEMON", "PORTA", "ZEBRAS", "CADENUS", "NICODEMUS", "PHILLIPS", "SLIDE", "KEYWORD", "RAGBABY", "PRESIDENT", "FRANCE", "ARMY", "ALPHA", "OMEGA"]
    for _, word in keyWords {
        if InStr(preset, word) {
            keyEdit.Value := word
            did := true
            break
        }
    }

    if InStr(preset, "Gronsfeld") || InStr(preset, "Gromark") || InStr(preset, "Swagman") || InStr(preset, "digit") || InStr(preset, "number") {
        if !did || keyEdit.Value = "LEMON"
            keyEdit.Value := "31415"
        did := true
    }

    if InStr(preset, "Affine") || InStr(preset, "Decimation") || InStr(preset, "Multiplicative") {
        if RegExMatch(preset, "i)(?:x|mod|Decimation\s+)(\d+)", &aMatch) {
            aVal := Integer(aMatch[1])
            if IsValidAffineA(aVal)
                affineAEdit.Value := aVal
        }
        if affineAEdit.Value = ""
            affineAEdit.Value := "5"
        if affineBEdit.Value = ""
            affineBEdit.Value := "8"
        did := true
    }

    if InStr(preset, "Caesar") && shiftEdit.Value = ""
        shiftEdit.Value := "3"
    if (InStr(preset, "Vigenere") || InStr(preset, "Beaufort") || InStr(preset, "Porta") || InStr(preset, "Bellaso") || InStr(preset, "Alberti")) && keyEdit.Value = ""
        keyEdit.Value := "CIPHER"

    return did
}

FinishPresetApply(preset) {
    ApplySettingsCore(false)
    ResetState()
    UpdateStatus()
    ToolTip "Preset applied: " . preset
    SetTimer () => ToolTip(), -1200
}

SetEnigmaPreset(model, thin, left, middle, right, reflector, start, rings, plugPairs) {
    global modeName, searchBox, modeBox, displayedModeList, thinBox, leftBox, middleBox, rightBox, reflectorBox, startEdit, ringsEdit, plugboardEdit
    global THIN_ROTOR_NAMES, ROTOR_NAMES

    modeName := model
    searchBox.Value := ""
    FilterModeList("")
    modeBox.Choose(IndexOf(displayedModeList, model))
    UpdateModePanel()

    thinBox.Choose(IndexOf(THIN_ROTOR_NAMES, thin))
    leftBox.Choose(IndexOf(ROTOR_NAMES, left))
    middleBox.Choose(IndexOf(ROTOR_NAMES, middle))
    rightBox.Choose(IndexOf(ROTOR_NAMES, right))
    RefreshReflectorList()
    reflectorBox.Choose(IndexOf(CurrentReflectorList(), reflector))
    startEdit.Value := start
    ringsEdit.Value := rings
    plugboardEdit.Value := plugPairs
}


ApplyQuagmirePreset(preset) {
    global modeName, searchBox, modeBox, displayedModeList
    global quagPlainEdit, quagCipherEdit, quagIndicatorEdit, quagPositionBox, ALPHABET

    if InStr(preset, "Quagmire I")
        modeName := "Quagmire I"
    else if InStr(preset, "Quagmire II")
        modeName := "Quagmire II"
    else if InStr(preset, "Quagmire III")
        modeName := "Quagmire III"
    else
        modeName := "Quagmire IV"

    searchBox.Value := ""
    FilterModeList("")
    modeBox.Choose(IndexOf(displayedModeList, modeName))
    UpdateModePanel()

    if InStr(preset, "random") {
        quagPlainEdit.Value := RandomLetters(Random(5, 12))
        quagCipherEdit.Value := RandomLetters(Random(5, 12))
        quagIndicatorEdit.Value := RandomLetters(Random(5, 10))
        quagPositionBox.Choose(Random(1, 26))
        return
    }

    if InStr(preset, "KRYPTOS") {
        quagPlainEdit.Value := "KRYPTOS"
        quagCipherEdit.Value := "PALIMPSEST"
        quagIndicatorEdit.Value := "ABSCISSA"
        quagPositionBox.Choose(IndexOf(StrSplit(ALPHABET), "K"))
        return
    }

    if InStr(preset, "MONARCHY") {
        quagPlainEdit.Value := "MONARCHY"
        quagCipherEdit.Value := "MONARCHY"
        quagIndicatorEdit.Value := "SEARCH"
        quagPositionBox.Choose(1)
        return
    }

    quagPlainEdit.Value := "CIPHER"
    quagCipherEdit.Value := "MONARCHY"
    quagIndicatorEdit.Value := "SECRET"
    quagPositionBox.Choose(1)
}

ApplyRandomEnigmaPreset(model) {
    global REFLECTOR_M3_NAMES, REFLECTOR_M4_NAMES, THIN_ROTOR_NAMES
    rotors := RandomRotorSelection(3)
    thin := THIN_ROTOR_NAMES[Random(1, THIN_ROTOR_NAMES.Length)]
    reflectorList := (model = "Enigma M4") ? REFLECTOR_M4_NAMES : REFLECTOR_M3_NAMES
    reflector := reflectorList[Random(1, reflectorList.Length)]
    lenNeeded := (model = "Enigma M4") ? 4 : 3
    start := RandomLetters(lenNeeded)
    rings := RandomLetters(lenNeeded)
    plugs := RandomPlugboardPairs(Random(5, 10))
    SetEnigmaPreset(model, thin, rotors[1], rotors[2], rotors[3], reflector, start, rings, plugs)
}

RandomRotorSelection(count) {
    global ROTOR_NAMES
    pool := ROTOR_NAMES.Clone()
    out := []
    Loop count {
        idx := Random(1, pool.Length)
        out.Push(pool[idx])
        pool.RemoveAt(idx)
    }
    return out
}

RandomPlugboardPairs(pairCount := 10) {
    global ALPHABET
    letters := StrSplit(ALPHABET)
    pairs := []
    Loop Min(pairCount, 13) {
        if letters.Length < 2
            break
        i := Random(1, letters.Length)
        a := letters.RemoveAt(i)
        j := Random(1, letters.Length)
        b := letters.RemoveAt(j)
        pairs.Push(a . b)
    }
    out := ""
    for i, pair in pairs
        out .= (i = 1 ? "" : " ") . pair
    return out
}

RandomLetters(length) {
    global ALPHABET
    out := ""
    Loop length
        out .= SubStr(ALPHABET, Random(1, 26), 1)
    return out
}

RandomDigits(length) {
    out := ""
    Loop length
        out .= Random(0, 9)
    return out
}

; ------------------------------------------------------------
; Mode-specific settings visibility
; ------------------------------------------------------------

UpdateModePanel() {
    global modeName, allSettingControls, enigmaPanelControls, enigmaM4OnlyControls, caesarPanelControls, keyPanelControls, affinePanelControls, substitutionPanelControls, quagmirePanelControls, quagPlainControls, quagCipherControls, quagIndicatorControls
    global settingHintText

    SetControlsVisible(allSettingControls, false)

    if modeName = "Enigma M3" || modeName = "Enigma M4" {
        SetControlsVisible(enigmaPanelControls, true)
        SetControlsVisible(enigmaM4OnlyControls, modeName = "Enigma M4")
        RefreshReflectorList()
        if modeName = "Enigma M4"
            settingHintText.Value := "Enigma M4 settings: thin rotor, three stepping rotors, thin reflector, ring settings, start positions, and plugboard."
        else
            settingHintText.Value := "Enigma M3 settings: three stepping rotors, standard reflector, ring settings, start positions, and plugboard."
    } else if modeName = "Bazeries block" || modeName = "Reading order route block" || modeName = "Caesar custom alphabet" || modeName = "Della Porta disk" || modeName = "Keyed Caesar" || modeName = "Keyed alphabet Caesar" || modeName = "Keyed progressive Caesar" || modeName = "Progressive key Vigenere" {
        SetControlsVisible(caesarPanelControls, true)
        SetControlsVisible(keyPanelControls, true)
        settingHintText.Value := "This mode uses both the shift/number field and the key field."
    } else if modeName = "Caesar" || modeName = "Progressive Caesar" || modeName = "Trithemius" || modeName = "Keyboard Caesar" || modeName = "Vowel Caesar" || modeName = "Consonant Caesar" || modeName = "Alternating Caesar" || modeName = "Rail fence block" || modeName = "Scytale transposition" || modeName = "Route cipher block" || modeName = "M-209 Hagelin style" || modeName = "Boustrophedon route block" || modeName = "Spiral inward route block" || modeName = "Spiral outward route block" || modeName = "Rotating square route block" {
        SetControlsVisible(caesarPanelControls, true)
        settingHintText.Value := "Shift settings: Caesar uses a fixed shift; Progressive Caesar and Trithemius use this as the starting shift."
    } else if IsQuagmireMode(modeName) {
        SetControlsVisible(quagmirePanelControls, true)
        ; Hide unused Quagmire alphabet fields per variant.
        if modeName = "Quagmire I" {
            SetControlsVisible(quagCipherControls, false)
            settingHintText.Value := "Quagmire I: keyed plaintext alphabet + normal ciphertext alphabet + indicator key/position."
        } else if modeName = "Quagmire II" {
            SetControlsVisible(quagPlainControls, false)
            settingHintText.Value := "Quagmire II: normal plaintext alphabet + keyed ciphertext alphabet + indicator key/position."
        } else if modeName = "Quagmire III" {
            SetControlsVisible(quagCipherControls, false)
            settingHintText.Value := "Quagmire III: keyed alphabet + indicator key/position."
        } else {
            settingHintText.Value := "Quagmire IV: separate plaintext alphabet key, ciphertext alphabet key, indicator key, and indicator position."
        }
    } else if modeName = "Vigenere" || modeName = "Autokey Vigenere" || modeName = "Gronsfeld" || modeName = "Running Key Vigenere" || modeName = "Beaufort" || modeName = "Variant Beaufort" || modeName = "Porta" || modeName = "Keyword substitution" || modeName = "XOR hex with key" || modeName = "XOR binary with key" || modeName = "Condi" || modeName = "Playfair pairs" || modeName = "Bifid pairs" || modeName = "Two-square pairs" || modeName = "Four-square pairs" || modeName = "Nihilist substitution" || modeName = "Progressive Vigenere" || modeName = "Quagmire I" || modeName = "Quagmire II" || modeName = "Quagmire III" || modeName = "Quagmire IV" || modeName = "Alberti disk" || modeName = "Bellaso" || modeName = "Autokey Beaufort" || modeName = "Progressive Porta" || modeName = "Gronsfeld progressive" || modeName = "Keyed Atbash" || modeName = "Diana cipher" || modeName = "Keyed Polybius square" || modeName = "Keyed ADFGX" || modeName = "Keyed ADFGVX" || modeName = "Morbit Morse" || modeName = "Fractionated Morse" || modeName = "Kamasutra substitution" || modeName = "Phillips cipher" || modeName = "Slidefair pairs" || modeName = "Columnar transposition block" || modeName = "Double columnar block" || modeName = "Myszkowski transposition block" || modeName = "Jefferson disk" || modeName = "M-94 cylinder style" || modeName = "Bazeries cylinder style" || modeName = "VIC checkerboard" || modeName = "One-time pad A-Z" || modeName = "Vernam XOR 5-bit" || modeName = "RC4 hex stream" || modeName = "Solitaire/Pontifex" || modeName = "Bifid full period" || modeName = "Trifid full period" || modeName = "Nihilist numeric stream" || modeName = "Book cipher index" || modeName = "Ragbaby" || modeName = "Nicodemus block" || modeName = "Clave" || modeName = "Gromark" || modeName = "Seriated Playfair pairs" || modeName = "Playfair 6x6 pairs" || modeName = "Two-square vertical pairs" || modeName = "Tri-square triples" || modeName = "Two-square 6x6 pairs" || modeName = "Four-square 6x6 pairs" || modeName = "Bifid 6x6 pairs" || modeName = "Hill 3x3 block" || modeName = "Cadenus block" || modeName = "AMSCO block" || modeName = "Swagman block" || modeName = "Disrupted transposition block" || modeName = "Incomplete columnar block" || modeName = "Complete columnar block" || modeName = "Alternating columnar block" || modeName = "Reading order route block" || modeName = "Grille mask block" || modeName = "Fleissner grille block" || modeName = "ADFGVX escaped" || modeName = "Lorenz SZ40 toy stream" || modeName = "Hagelin C-series toy stream" || modeName = "Playfair Q omitted pairs" || modeName = "Double Playfair pairs" || modeName = "Twin Bifid pairs" || modeName = "Polybius columnar block" || modeName = "Bacon biliteral custom" || modeName = "Acrostic cover words" || modeName = "Interrupted key Vigenere" || modeName = "Variant Beaufort Autokey" || modeName = "Running key book" || modeName = "Progressive Beaufort" || modeName = "Progressive Variant Beaufort" || modeName = "Porta Autokey" || modeName = "Polybius 0-based keyed" || modeName = "Polybius letter coords keyed" || modeName = "Grandpre coordinate" || modeName = "Fractionated Polybius token" || modeName = "Vigenere keyed alphabet" || modeName = "Beaufort keyed alphabet" || modeName = "Variant Beaufort keyed alphabet" || modeName = "Autokey keyed alphabet" || modeName = "Porta numeric table" || modeName = "Porta reverse table" || modeName = "Atbash then Vigenere" || modeName = "Vigenere then Atbash" || modeName = "Running Atbash key" || modeName = "Autokey Atbash" || (IsV28RealWorldMode(modeName) || IsV29RealWorldMode(modeName) || IsV30RealWorldMode(modeName) || IsV31RealWorldMode(modeName) || IsV32MoreMode(modeName) || IsV33RealWorldMode(modeName) || IsV34RealWorldMode(modeName) || IsV37RealWorldMode(modeName) || IsV38RealWorldMode(modeName) || IsV39RealWorldMode(modeName) || IsV40RealWorldMode(modeName)) {
        SetControlsVisible(keyPanelControls, true)
        settingHintText.Value := "Key settings: this cipher only uses the key field. Gronsfeld expects digits; XOR uses the key bytes; the others expect letters."
    } else if modeName = "Affine" {
        SetControlsVisible(affinePanelControls, true)
        settingHintText.Value := "Affine settings: choose a and b."
    } else if modeName = "Random substitution" {
        SetControlsVisible(substitutionPanelControls, true)
        settingHintText.Value := "Random substitution settings: choose or randomize the 26-letter substitution alphabet."
    } else {
        settingHintText.Value := "This mode has no extra cipher-specific settings."
    }

    ; Final cleanup: generated historical/style modes are often routed through a
    ; shared transformer, but many of them do not actually require a user key.
    ; Hide the key row unless the selected mode is a real keyed/key-like family.
    if ModeShouldHideKeyPanel(modeName) {
        SetControlsVisible(keyPanelControls, false)
        if InStr(settingHintText.Value, "Key settings:")
            settingHintText.Value := "This mode has no extra cipher-specific settings."
    }
}

ModeShouldHideKeyPanel(name) {
    if ModeActuallyUsesKey(name)
        return false

    ; These generated groups previously forced the key panel for every entry.
    ; Only entries matched by ModeActuallyUsesKey() should keep it visible.
    return (IsV28RealWorldMode(name)
        || IsV29RealWorldMode(name)
        || IsV30RealWorldMode(name)
        || IsV31RealWorldMode(name)
        || IsV32MoreMode(name)
        || IsV33RealWorldMode(name)
        || IsV34RealWorldMode(name)
        || IsV37RealWorldMode(name)
        || IsV38RealWorldMode(name)
        || IsV39RealWorldMode(name)
        || IsV40RealWorldMode(name))
}

ModeActuallyUsesKey(name) {
    ; Exact base modes whose settings genuinely include a key or keyword.
    keyedModes := [
        "Vigenere", "Autokey Vigenere", "Running Key Vigenere", "Beaufort", "Variant Beaufort", "Porta", "Keyword substitution",
        "Condi", "Playfair pairs", "Bifid pairs", "Two-square pairs", "Four-square pairs", "Nihilist substitution", "Progressive Vigenere",
        "Alberti disk", "Bellaso", "Autokey Beaufort", "Progressive Porta", "Gronsfeld progressive", "Keyed Atbash", "Diana cipher",
        "Keyed Polybius square", "Keyed ADFGX", "Keyed ADFGVX", "Morbit Morse", "Fractionated Morse", "Kamasutra substitution", "Phillips cipher", "Slidefair pairs",
        "Columnar transposition block", "Double columnar block", "Myszkowski transposition block", "Jefferson disk", "M-94 cylinder style", "Bazeries cylinder style",
        "VIC checkerboard", "One-time pad A-Z", "Vernam XOR 5-bit", "RC4 hex stream", "Solitaire/Pontifex", "Bifid full period", "Trifid full period",
        "Nihilist numeric stream", "Book cipher index", "Ragbaby", "Nicodemus block", "Clave", "Gromark", "Seriated Playfair pairs", "Playfair 6x6 pairs",
        "Two-square vertical pairs", "Tri-square triples", "Two-square 6x6 pairs", "Four-square 6x6 pairs", "Bifid 6x6 pairs", "Hill 3x3 block",
        "Cadenus block", "AMSCO block", "Swagman block", "Disrupted transposition block", "Incomplete columnar block", "Complete columnar block", "Alternating columnar block",
        "Reading order route block", "Grille mask block", "Fleissner grille block", "ADFGVX escaped", "Lorenz SZ40 toy stream", "Hagelin C-series toy stream",
        "Playfair Q omitted pairs", "Double Playfair pairs", "Twin Bifid pairs", "Polybius columnar block", "Bacon biliteral custom", "Acrostic cover words",
        "Keyed Caesar", "Keyed alphabet Caesar", "Keyed progressive Caesar", "Interrupted key Vigenere", "Progressive key Vigenere", "Variant Beaufort Autokey",
        "Running key book", "Progressive Beaufort", "Progressive Variant Beaufort", "Porta Autokey", "Polybius 0-based keyed", "Polybius letter coords keyed",
        "Grandpre coordinate", "Fractionated Polybius token", "Vigenere keyed alphabet", "Beaufort keyed alphabet", "Variant Beaufort keyed alphabet", "Autokey keyed alphabet",
        "Porta numeric table", "Porta reverse table", "Atbash then Vigenere", "Vigenere then Atbash", "Running Atbash key", "Autokey Atbash",
        "XOR hex with key", "XOR binary with key", "Gronsfeld"
    ]
    for _, item in keyedModes {
        if name = item
            return true
    }

    ; Keyword-based family detection for generated real-world labels.
    ; Avoid broad words like "alphabet", "symbol", or "token" because those often
    ; describe fixed visual/code alphabets that need no user setting.
    return ModeNameContainsAny(name, [
        "Keyed", " key", "daily key", "officer key", "weather key", "training key", "one-time pad", "OTP", "Vernam", "Vigenere", "Beaufort", "Gronsfeld",
        "Porta", "Portax", "Autokey", "Bellaso", "Diana", "Quagmire", "Condi", "Chaocipher", "Gromark", "Ragbaby", "Nicodemus",
        "Cadenus", "AMSCO", "Swagman", "Myszkowski", "Columnar", "UBCHI", "Playfair", "Doppelkasten", "Two-square", "Four-square", "Tri-square",
        "Bifid", "Trifid", "Delastelle", "Digrafid", "Nihilist", "ADFGX", "ADFGVX", "VIC", "Straddling", "Monome", "Polybius keyed",
        "Hill", "Jefferson", "M-94", "M-138", "Bazeries", "Book cipher", "Codebook", "Solitaire", "RC4", "ARCFOUR", "Lorenz", "Hagelin", "M-209",
        "Enigma", "Typex", "SIGABA", "NEMA", "Fialka", "KL-7", "Hebern", "Kryha", "Purple", "Siemens", "KW-", "Rockex", "SIGTOT", "cipher disk", "wheel daily", "rotor"
    ])
}

ModeNameContainsAny(haystack, needles) {
    for _, needle in needles {
        if InStr(haystack, needle)
            return true
    }
    return false
}

SetControlsVisible(ctrls, visible) {
    for _, ctrl in ctrls {
        try ctrl.Opt(visible ? "-Hidden" : "+Hidden")
    }
}

RefreshReflectorList() {
    global reflectorBox, modeName, REFLECTOR_M3_NAMES, REFLECTOR_M4_NAMES
    currentList := CurrentReflectorList()
    currentText := ""
    try currentText := reflectorBox.Text
    try reflectorBox.Delete()
    reflectorBox.Add(currentList)
    idx := IndexOf(currentList, currentText)
    reflectorBox.Choose(idx)
}

CurrentReflectorList() {
    global modeName, REFLECTOR_M3_NAMES, REFLECTOR_M4_NAMES
    if modeName = "Enigma M4"
        return REFLECTOR_M4_NAMES
    return REFLECTOR_M3_NAMES
}

; ------------------------------------------------------------
; Settings actions
; ------------------------------------------------------------

EnableClicked(*) {
    global enabled, enableBox, autoResetBox, autoResetOnEnable
    old := enabled
    enabled := enableBox.Value = 1
    autoResetOnEnable := autoResetBox.Value = 1
    ApplySettingsCore(false)
    if enabled && !old && autoResetOnEnable
        ResetState()
    UpdateStatus()
}

ApplySettingsClicked(*) {
    ApplySettingsCore(true)
}

ApplySettingsCore(showTip := true) {
    global searchBox, modeBox, displayedModeList, modeName, enabled, enableBox, autoResetBox, autoResetOnEnable
    global thinBox, leftBox, middleBox, rightBox, reflectorBox, startEdit, ringsEdit, plugboardEdit
    global THIN_ROTOR_NAMES, ROTOR_NAMES, enigmaThin, enigmaLeft, enigmaMiddle, enigmaRight, enigmaReflector, enigmaStart, enigmaRings, plugboardPairs, plugboard
    global shiftEdit, keyEdit, affineAEdit, affineBEdit, substitutionEdit, outputModeBox
    global quagPlainEdit, quagCipherEdit, quagIndicatorEdit, quagPositionBox, quagPlainKey, quagCipherKey, quagIndicatorKey, quagIndicatorPos, ALPHABET
    global shiftValue, keyText, affineA, affineB, substitutionAlphabet, outputMode

    selectedMode := SelectedFrom(modeBox, displayedModeList)
    if selectedMode != "No ciphers found"
        modeName := selectedMode
    UpdateModePanel()

    enigmaThin := SelectedFrom(thinBox, THIN_ROTOR_NAMES)
    enigmaLeft := SelectedFrom(leftBox, ROTOR_NAMES)
    enigmaMiddle := SelectedFrom(middleBox, ROTOR_NAMES)
    enigmaRight := SelectedFrom(rightBox, ROTOR_NAMES)
    enigmaReflector := SelectedFrom(reflectorBox, CurrentReflectorList())

    lenNeeded := (modeName = "Enigma M4") ? 4 : 3
    enigmaStart := NormalizeLettersToLength(startEdit.Value, lenNeeded, "A")
    startEdit.Value := enigmaStart
    enigmaRings := NormalizeLettersToLength(ringsEdit.Value, lenNeeded, "A")
    ringsEdit.Value := enigmaRings

    plugboardPairs := plugboardEdit.Value
    plugboard := BuildPlugboard(plugboardPairs)

    shiftValue := ToIntegerOrDefault(shiftEdit.Value, 3)
    shiftEdit.Value := shiftValue

    keyText := keyEdit.Value
    if modeName = "Gronsfeld" || modeName = "Gronsfeld progressive" {
        if CleanDigits(keyText) = "" {
            keyText := "31415"
            keyEdit.Value := keyText
        }
    } else if modeName = "Morbit Morse" {
        if CleanDigits(keyText) = "" {
            keyText := "123456789"
            keyEdit.Value := keyText
        }
    } else if modeName = "Vigenere" || modeName = "Autokey Vigenere" || modeName = "Running Key Vigenere" || modeName = "Beaufort" || modeName = "Variant Beaufort" || modeName = "Porta" || modeName = "Keyword substitution" || modeName = "Condi" || modeName = "Playfair pairs" || modeName = "Bifid pairs" || modeName = "Two-square pairs" || modeName = "Four-square pairs" || modeName = "Nihilist substitution" || modeName = "Progressive Vigenere" || modeName = "Quagmire I" || modeName = "Quagmire II" || modeName = "Quagmire III" || modeName = "Quagmire IV" || modeName = "Alberti disk" || modeName = "Bellaso" || modeName = "Autokey Beaufort" || modeName = "Progressive Porta" || modeName = "Gronsfeld progressive" || modeName = "Keyed Atbash" || modeName = "Diana cipher" || modeName = "Keyed Polybius square" || modeName = "Keyed ADFGX" || modeName = "Keyed ADFGVX" || modeName = "Fractionated Morse" || modeName = "Kamasutra substitution" || modeName = "Phillips cipher" || modeName = "Slidefair pairs" || modeName = "Columnar transposition block" || modeName = "Double columnar block" || modeName = "Myszkowski transposition block" || modeName = "Jefferson disk" || modeName = "M-94 cylinder style" || modeName = "Bazeries cylinder style" || modeName = "VIC checkerboard" || modeName = "One-time pad A-Z" || modeName = "Vernam XOR 5-bit" || modeName = "RC4 hex stream" || modeName = "Solitaire/Pontifex" || modeName = "Bifid full period" || modeName = "Trifid full period" || modeName = "Nihilist numeric stream" || modeName = "Book cipher index" || modeName = "Keyed Caesar" || modeName = "Keyed alphabet Caesar" || modeName = "Keyed progressive Caesar" || modeName = "Interrupted key Vigenere" || modeName = "Progressive key Vigenere" || modeName = "Variant Beaufort Autokey" || modeName = "Running key book" || modeName = "Progressive Beaufort" || modeName = "Progressive Variant Beaufort" || modeName = "Porta Autokey" || modeName = "Polybius 0-based keyed" || modeName = "Polybius letter coords keyed" || modeName = "Grandpre coordinate" || modeName = "Fractionated Polybius token" || modeName = "Vigenere keyed alphabet" || modeName = "Beaufort keyed alphabet" || modeName = "Variant Beaufort keyed alphabet" || modeName = "Autokey keyed alphabet" || modeName = "Porta numeric table" || modeName = "Porta reverse table" || modeName = "Atbash then Vigenere" || modeName = "Vigenere then Atbash" || modeName = "Running Atbash key" || modeName = "Autokey Atbash" || (IsV28RealWorldMode(modeName) || IsV29RealWorldMode(modeName) || IsV30RealWorldMode(modeName) || IsV31RealWorldMode(modeName) || IsV32MoreMode(modeName) || IsV33RealWorldMode(modeName) || IsV34RealWorldMode(modeName) || IsV37RealWorldMode(modeName) || IsV38RealWorldMode(modeName) || IsV39RealWorldMode(modeName) || IsV40RealWorldMode(modeName)) {
        if CleanLetters(keyText) = "" {
            keyText := "KEY"
            keyEdit.Value := keyText
        }
    } else if modeName = "XOR hex with key" || modeName = "XOR binary with key" || modeName = "RC4 hex stream" {
        if keyText = "" {
            keyText := "KEY"
            keyEdit.Value := keyText
        }
    }

    quagPlainKey := CleanLetters(quagPlainEdit.Value)
    if quagPlainKey = ""
        quagPlainKey := "CIPHER"
    quagPlainEdit.Value := quagPlainKey

    quagCipherKey := CleanLetters(quagCipherEdit.Value)
    if quagCipherKey = ""
        quagCipherKey := "MONARCHY"
    quagCipherEdit.Value := quagCipherKey

    quagIndicatorKey := CleanLetters(quagIndicatorEdit.Value)
    if quagIndicatorKey = ""
        quagIndicatorKey := "SECRET"
    quagIndicatorEdit.Value := quagIndicatorKey

    quagIndicatorPos := SelectedFrom(quagPositionBox, StrSplit(ALPHABET))

    affineA := ToIntegerOrDefault(affineAEdit.Value, 5)
    affineB := ToIntegerOrDefault(affineBEdit.Value, 8)
    if !IsValidAffineA(affineA) {
        affineA := 5
        affineAEdit.Value := "5"
    }
    affineB := PositiveMod(affineB, 26)
    affineBEdit.Value := affineB

    substitutionAlphabet := NormalizeSubstitutionAlphabet(substitutionEdit.Value)
    substitutionEdit.Value := substitutionAlphabet

    outputMode := SelectedFrom(outputModeBox, ["Preserve typed case", "UPPERCASE", "lowercase"])
    autoResetOnEnable := autoResetBox.Value = 1
    enabled := enableBox.Value = 1

    ResetState()
    UpdateStatus()

    if showTip {
        ToolTip "Settings applied"
        SetTimer () => ToolTip(), -900
    }
}

RandomizeSubstitutionClicked(*) {
    global substitutionEdit
    substitutionEdit.Value := RandomAlphabet()
    ApplySettingsCore(false)
    ToolTip "Random substitution alphabet generated"
    SetTimer () => ToolTip(), -1000
}

ResetStateClicked(*) {
    ResetState()
    UpdateStatus()
    ToolTip "State reset"
    SetTimer () => ToolTip(), -900
}

PreviewClicked(*) {
    global previewInput, previewOutput, rotorPositions, streamIndex, autoKeyHistory, pairBuffer, condiShift, chaosLeft, chaosRight

    ApplySettingsCore(false)

    savedPositions := rotorPositions.Clone()
    savedStream := streamIndex
    savedHistory := autoKeyHistory
    savedPairBuffer := pairBuffer
    savedCondiShift := condiShift
    savedChaosLeft := chaosLeft
    savedChaosRight := chaosRight

    ResetState()
    text := previewInput.Value
    out := ""

    for _, ch in StrSplit(text) {
        if StrUpper(ch) ~= "^[A-Z]$"
            out .= EncryptLetterByMode(ch)
        else
            out .= ch
    }
    out .= FlushPendingByMode()

    previewOutput.Value := out

    rotorPositions := savedPositions
    streamIndex := savedStream
    autoKeyHistory := savedHistory
    pairBuffer := savedPairBuffer
    condiShift := savedCondiShift
    chaosLeft := savedChaosLeft
    chaosRight := savedChaosRight
    UpdateStatus()
}

ToggleEnabledFromHotkey() {
    global enabled, enableBox, autoResetOnEnable
    ; Read current GUI settings first, so hotkey toggling uses the visible settings.
    try ApplySettingsCore(false)
    enabled := !enabled
    if enabled && autoResetOnEnable
        ResetState()
    try enableBox.Value := enabled ? 1 : 0
    UpdateStatus()
    ToolTip "Live cipher: " . (enabled ? "ON" : "OFF")
    SetTimer () => ToolTip(), -1000
}

ResetStateFromHotkey() {
    ResetState()
    UpdateStatus()
    ToolTip "Cipher state reset"
    SetTimer () => ToolTip(), -1000
}

ResetState() {
    global rotorPositions, enigmaStart, enigmaRings, modeName, streamIndex, autoKeyHistory, pairBuffer, condiShift, chaosLeft, chaosRight, chaosLeftDefault, chaosRightDefault, keyText
    lenNeeded := (modeName = "Enigma M4") ? 4 : 3
    enigmaStart := NormalizeLettersToLength(enigmaStart, lenNeeded, "A")
    enigmaRings := NormalizeLettersToLength(enigmaRings, lenNeeded, "A")
    rotorPositions := StrSplit(enigmaStart)
    streamIndex := 0
    autoKeyHistory := ""
    pairBuffer := ""
    condiShift := 0
    chaosLeft := chaosLeftDefault
    chaosRight := chaosRightDefault
    InitSolitaireDeck(keyText)
    InitRC4(keyText)
}

UpdateStatus() {
    global enabled, statusText, stateText, modeName, streamIndex
    try statusText.Value := "Status: " . (enabled ? "ON — typing in other apps is transformed" : "OFF — typing is normal") . " | Mode: " . modeName
    try stateText.Value := "State: enigma positions=" . PositionsToString() . " | stream index=" . streamIndex
}

; ------------------------------------------------------------
; Keyboard behavior
; ------------------------------------------------------------

IsEncryptionActive() {
    global enabled, mainGui
    if !enabled
        return false
    try {
        if WinActive("ahk_id " mainGui.Hwnd)
            return false
    }
    if GetKeyState("Ctrl", "P") || GetKeyState("Alt", "P") || GetKeyState("LWin", "P") || GetKeyState("RWin", "P")
        return false
    return true
}

SendEncrypted(baseLetter, shifted) {
    caps := GetKeyState("CapsLock", "T")
    typedUpper := caps != shifted
    original := typedUpper ? StrUpper(baseLetter) : StrLower(baseLetter)
    encrypted := EncryptLetterByMode(original)
    encrypted := ApplyOutputCase(encrypted, original)
    SendText encrypted
    UpdateStatus()
}

SendBoundaryKey(keyTextToSend, sendAsKey := false) {
    ; Flush pending pair/block ciphers before spaces, Enter, or Tab.
    pending := FlushPendingByMode()
    if pending != ""
        SendText pending
    if sendAsKey
        Send keyTextToSend
    else
        SendText keyTextToSend
    UpdateStatus()
}

HandleBackspaceKey() {
    global pairBuffer
    ; If a pair/block cipher is buffering letters which were not output yet, erase the buffer first.
    if pairBuffer != "" {
        pairBuffer := SubStr(pairBuffer, 1, Max(0, StrLen(pairBuffer) - 1))
        UpdateStatus()
        return
    }
    Send "{Backspace}"
    UpdateStatus()
}

ApplyOutputCase(text, original) {
    global outputMode
    if outputMode = "UPPERCASE"
        return StrUpper(text)
    if outputMode = "lowercase"
        return StrLower(text)
    if original ~= "^[a-z]$"
        return StrLower(text)
    return StrUpper(text)
}

; ------------------------------------------------------------
; Mode dispatcher
; ------------------------------------------------------------

EncryptLetterByMode(letter) {
    global modeName, shiftValue, keyText, affineA, affineB, substitutionAlphabet, streamIndex, autoKeyHistory
    upper := StrUpper(letter)

    ; The live hotkeys feed letters only.  The startup self-check may include
    ; boundary/digit characters, so return those unchanged instead of sending
    ; them into alphabet-only cipher tables.
    if !(upper ~= "^[A-Z]$")
        return letter

    if IsV40RealWorldMode(modeName)
        return V40RealWorldLetter(letter)

    if IsV39RealWorldMode(modeName)
        return V39RealWorldLetter(letter)

    if IsV38RealWorldMode(modeName)
        return V38RealWorldLetter(letter)

    if IsV37RealWorldMode(modeName)
        return V37RealWorldLetter(letter)

    if IsV34RealWorldMode(modeName)
        return V34RealWorldLetter(letter)

    if IsV33RealWorldMode(modeName)
        return V33RealWorldLetter(letter)

    if IsV32MoreMode(modeName)
        return V32MoreLetter(letter)

    if IsV31RealWorldMode(modeName)
        return V31RealWorldLetter(letter)

    if IsV30RealWorldMode(modeName)
        return V30RealWorldLetter(letter)

    switch modeName {
        case "Enigma M3", "Enigma M4":
            return EnigmaEncryptLetter(letter)
        case "Caesar":
            return ShiftLetter(letter, shiftValue)
        case "Progressive Caesar", "Trithemius":
            shift := shiftValue + streamIndex
            streamIndex += 1
            return ShiftLetter(letter, shift)
        case "ROT13":
            return ShiftLetter(letter, 13)
        case "Atbash":
            return AtbashLetter(letter)
        case "Vigenere", "Running Key Vigenere":
            shift := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return ShiftLetter(letter, shift)
        case "Autokey Vigenere":
            shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
            streamIndex += 1
            autoKeyHistory .= upper
            return ShiftLetter(letter, shift)
        case "Gronsfeld":
            shift := DigitShiftAt(keyText, streamIndex)
            streamIndex += 1
            return ShiftLetter(letter, shift)
        case "Beaufort":
            shift := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(shift - LetterIndex(upper), 26), IsUpperLetter(letter))
        case "Variant Beaufort":
            shift := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return ShiftLetter(letter, -shift)
        case "Porta":
            kidx := Floor(KeyShiftAt(keyText, streamIndex) / 2)
            streamIndex += 1
            x := LetterIndex(upper)
            if x < 13
                y := PositiveMod(x + 13 - kidx, 13) + 13
            else
                y := PositiveMod(x - 13 + kidx, 13)
            return LetterFromIndex(y, IsUpperLetter(letter))
        case "Affine":
            x := LetterIndex(upper)
            y := PositiveMod((affineA * x) + affineB, 26)
            return LetterFromIndex(y, IsUpperLetter(letter))
        case "Keyword substitution":
            alpha := KeywordAlphabet(keyText)
            return SubstituteFromAlphabet(letter, alpha)
        case "Random substitution":
            return SubstituteFromAlphabet(letter, substitutionAlphabet)
        case "QWERTY to Dvorak":
            return DvorakLetter(letter)
        case "QWERTY to AZERTY":
            return AzertyLetter(letter)
        case "Keyboard mirror":
            return KeyboardMirrorLetter(letter)
        case "Leet basic":
            return LeetLetter(letter)
        case "Morse letters":
            return MorseLetter(letter)
        case "Binary 5-bit":
            return Binary5Letter(letter)
        case "Baconian A/B":
            return BaconianLetter(letter)
        case "A1Z26 numbers":
            return A1Z26Letter(letter)
        case "Polybius square":
            return PolybiusLetter(letter)
        case "Tap code":
            return TapCodeLetter(letter)
        case "ADFGX":
            return ADFGXLetter(letter)
        case "ADFGVX":
            return ADFGVXLetter(letter)
        case "Straddling checkerboard":
            return StraddlingCheckerboardLetter(letter)
        case "Monome-Dinome":
            return MonomeDinomeLetter(letter)
        case "Pollux Morse":
            return PolluxMorseLetter(letter)
        case "Base64 per letter":
            return Base64PerLetter(letter)
        case "URL percent":
            return UrlPercentLetter(letter)
        case "HTML entity":
            return HtmlEntityLetter(letter)
        case "Unicode code point":
            return UnicodeCodePointLetter(letter)
        case "ASCII binary 8-bit":
            return AsciiBinary8Letter(letter)
        case "XOR hex with key":
            return XorHexLetter(letter)
        case "XOR binary with key":
            return XorBinaryLetter(letter)
        case "Braille":
            return BrailleLetter(letter)
        case "Pigpen symbols":
            return PigpenLetter(letter)
        case "Emoji alphabet":
            return EmojiLetter(letter)
        case "Letter index hex":
            return LetterIndexHexLetter(letter)
        case "Roman numerals":
            return RomanNumeralLetter(letter)
        case "Prime numbers":
            return PrimeNumberLetter(letter)
        case "Squared A1Z26":
            return SquaredA1Z26Letter(letter)
        case "Condi":
            return CondiLetter(letter)
        case "Chaocipher":
            return ChaocipherLetter(letter)
        case "Playfair pairs":
            return PlayfairLetter(letter)
        case "Hill 2x2 pairs":
            return Hill2x2Letter(letter)
        case "Bifid pairs":
            return BifidLetter(letter)
        case "Two-square pairs":
            return TwoSquareLetter(letter)
        case "Four-square pairs":
            return FourSquareLetter(letter)
        case "Nihilist substitution":
            return NihilistLetter(letter)
        case "Trifid coordinates":
            return TrifidCoordinateLetter(letter)
        case "Checkerboard coordinates":
            return CheckerboardCoordinateLetter(letter)
        case "Baudot ITA2":
            return BaudotLetter(letter)
        case "Gray code 5-bit":
            return GrayCode5Letter(letter)
        case "BCD A1Z26":
            return BcdA1Z26Letter(letter)
        case "Fibonacci numbers":
            return FibonacciNumberLetter(letter)
        case "Triangular numbers":
            return TriangularNumberLetter(letter)
        case "Cubed A1Z26":
            return CubedA1Z26Letter(letter)
        case "Factorial index":
            return FactorialIndexLetter(letter)
        case "Modulo 9 index":
            return Modulo9IndexLetter(letter)
        case "Reverse alphabet index":
            return ReverseAlphabetIndexLetter(letter)
        case "Keyboard Caesar":
            return KeyboardCaesarLetter(letter)
        case "Vowel Caesar":
            return VowelCaesarLetter(letter)
        case "Consonant Caesar":
            return ConsonantCaesarLetter(letter)
        case "Alternating Caesar":
            return AlternatingCaesarLetter(letter)
        case "Elder Futhark runes":
            return FutharkLetter(letter)
        case "Ogham letters":
            return OghamLetter(letter)
        case "Semaphore text":
            return SemaphoreTextLetter(letter)
        case "Masonic pigpen variant":
            return MasonicPigpenVariantLetter(letter)
        case "Progressive Vigenere":
            shift := KeyShiftAt(keyText, streamIndex) + streamIndex
            streamIndex += 1
            return ShiftLetter(letter, shift)
        case "Quagmire I":
            return QuagmireLetter(letter, 1)
        case "Quagmire II":
            return QuagmireLetter(letter, 2)
        case "Quagmire III":
            return QuagmireLetter(letter, 3)
        case "Quagmire IV":
            return QuagmireLetter(letter, 4)
        case "Alberti disk":
            return AlbertiDiskLetter(letter)
        case "Bellaso":
            return BellasoLetter(letter)
        case "Autokey Beaufort":
            return AutokeyBeaufortLetter(letter)
        case "Progressive Porta":
            return ProgressivePortaLetter(letter)
        case "Gronsfeld progressive":
            return GronsfeldProgressiveLetter(letter)
        case "Keyed Atbash":
            return KeyedAtbashLetter(letter)
        case "Diana cipher":
            return DianaLetter(letter)
        case "Random Caesar per letter":
            return ShiftLetter(letter, Random(1, 25))
        case "Fibonacci Caesar shift":
            return FibonacciCaesarShiftLetter(letter)
        case "Prime Caesar shift":
            return PrimeCaesarShiftLetter(letter)
        case "Homophonic numbers":
            return HomophonicNumberLetter(letter)
        case "Base32 per letter":
            return Base32PerLetter(letter)
        case "Quoted printable":
            return QuotedPrintableLetter(letter)
        case "Decimal A0Z25":
            return DecimalA0Z25Letter(letter)
        case "Zero padded A1Z26":
            return ZeroPaddedA1Z26Letter(letter)
        case "Octal A1Z26":
            return OctalA1Z26Letter(letter)
        case "Binary 6-bit index":
            return Binary6IndexLetter(letter)
        case "Coordinate 0-based":
            return Coordinate0BasedLetter(letter)
        case "Morse compact 01":
            return MorseCompact01Letter(letter)
        case "Polybius reversed":
            return PolybiusReversedLetter(letter)
        case "Maritime signal flags":
            return MaritimeFlagLetter(letter)
        case "Regional indicator symbols":
            return RegionalIndicatorLetter(letter)
        case "Circled letters":
            return CircledLetter(letter)
        case "Squared unicode letters":
            return SquaredUnicodeLetter(letter)
        case "Parenthesized letters":
            return ParenthesizedLetter(letter)
        case "Fraktur letters":
            return FrakturLetter(letter)
        case "Script letters":
            return ScriptLetter(letter)
        case "Small caps":
            return SmallCapsLetter(letter)
        case "Superscript letters":
            return SuperscriptLetter(letter)
        case "Subscript letters":
            return SubscriptLetter(letter)
        case "Zalgo light":
            return ZalgoLightLetter(letter)
        case "Mirror text alphabet":
            return MirrorTextAlphabetLetter(letter)
        case "Keyed Polybius square":
            return KeyedPolybiusLetter(letter)
        case "Keyed ADFGX":
            return KeyedADFGXLetter(letter)
        case "Keyed ADFGVX":
            return KeyedADFGVXLetter(letter)
        case "Morbit Morse":
            return MorbitMorseLetter(letter)
        case "Fractionated Morse":
            return FractionatedMorseLetter(letter)
        case "Morse reverse":
            return MorseReverseLetter(letter)
        case "Morse emoji":
            return MorseEmojiLetter(letter)
        case "Morse tap digits":
            return MorseTapDigitsLetter(letter)
        case "Baconian 24 I/J":
            return Baconian24Letter(letter)
        case "Kamasutra substitution":
            return KamasutraLetter(letter)
        case "Phillips cipher":
            return PhillipsLetter(letter)
        case "Slidefair pairs":
            return SlidefairLetter(letter)
        case "Colemak keyboard":
            return ColemakLetter(letter)
        case "QWERTZ keyboard":
            return QwertzLetter(letter)
        case "Keyboard adjacent right":
            return KeyboardAdjacentRightLetter(letter)
        case "Keyboard adjacent left":
            return KeyboardAdjacentLeftLetter(letter)
        case "Phone T9 digit":
            return PhoneT9DigitLetter(letter)
        case "Phone multitap":
            return PhoneMultitapLetter(letter)
        case "Chess coordinates":
            return ChessCoordinateLetter(letter)
        case "Dice pair code":
            return DicePairCodeLetter(letter)
        case "Domino tile code":
            return DominoTileCodeLetter(letter)
        case "Playing card code":
            return PlayingCardCodeLetter(letter)
        case "Base58 index":
            return Base58IndexLetter(letter)
        case "Base62 index":
            return Base62IndexLetter(letter)
        case "Crockford Base32 index":
            return CrockfordBase32IndexLetter(letter)
        case "Base85 per letter":
            return Base85PerLetter(letter)
        case "UUencode per letter":
            return UuencodePerLetter(letter)
        case "EBCDIC hex":
            return EBCDICHexLetter(letter)
        case "UTF-8 hex":
            return Utf8HexLetter(letter)
        case "UTF-16LE hex":
            return Utf16LEHexLetter(letter)
        case "HTML hex entity":
            return HtmlHexEntityLetter(letter)
        case "LCG checksum token":
            return LCGChecksumTokenLetter(letter)
        case "Knuth checksum token":
            return KnuthChecksumTokenLetter(letter)
        case "Hex ASCII":
            return HexAsciiLetter(letter)
        case "ASCII decimal":
            return AsciiDecimalLetter(letter)
        case "Octal ASCII":
            return OctalAsciiLetter(letter)
        case "Fullwidth letters":
            return FullwidthLetter(letter)
        case "Upside-down letters":
            return UpsideDownLetter(letter)
        case "Greek lookalike":
            return GreekLookalikeLetter(letter)
        case "Cyrillic lookalike":
            return CyrillicLookalikeLetter(letter)
        case "Rail fence block":
            return RailFenceBlockLetter(letter)
        case "Scytale transposition":
            return ScytaleBlockLetter(letter)
        case "Columnar transposition block":
            return ColumnarBlockLetter(letter)
        case "Double columnar block":
            return DoubleColumnarBlockLetter(letter)
        case "Route cipher block":
            return RouteCipherBlockLetter(letter)
        case "Myszkowski transposition block":
            return MyszkowskiBlockLetter(letter)
        case "Jefferson disk":
            return JeffersonDiskLetter(letter)
        case "M-94 cylinder style":
            return M94CylinderLetter(letter)
        case "Bazeries cylinder style":
            return BazeriesCylinderLetter(letter)
        case "M-209 Hagelin style":
            return M209HagelinLetter(letter)
        case "VIC checkerboard":
            return VICCheckerboardLetter(letter)
        case "One-time pad A-Z":
            return OneTimePadLetter(letter)
        case "Vernam XOR 5-bit":
            return VernamXor5BitLetter(letter)
        case "RC4 hex stream":
            return RC4HexStreamLetter(letter)
        case "Solitaire/Pontifex":
            return SolitairePontifexLetter(letter)
        case "Bifid full period":
            return BifidFullPeriodLetter(letter)
        case "Trifid full period":
            return TrifidFullPeriodLetter(letter)
        case "Nihilist numeric stream":
            return NihilistNumericStreamLetter(letter)
        case "Book cipher index":
            return BookCipherIndexLetter(letter)
        case "Ragbaby":
            return RagbabyLetter(letter)
        case "Nicodemus block":
            return NicodemusBlockLetter(letter)
        case "Clave":
            return ClaveLetter(letter)
        case "Gromark":
            return GromarkLetter(letter)
        case "Seriated Playfair pairs":
            return SeriatedPlayfairLetter(letter)
        case "Playfair 6x6 pairs":
            return Playfair6x6Letter(letter)
        case "Two-square vertical pairs":
            return TwoSquareVerticalLetter(letter)
        case "Tri-square triples":
            return TriSquareLetter(letter)
        case "Two-square 6x6 pairs":
            return TwoSquare6x6Letter(letter)
        case "Four-square 6x6 pairs":
            return FourSquare6x6Letter(letter)
        case "Bifid 6x6 pairs":
            return Bifid6x6Letter(letter)
        case "Hill 3x3 block":
            return Hill3x3BlockLetter(letter)
        case "Cadenus block":
            return CadenusBlockLetter(letter)
        case "AMSCO block":
            return AMSCOBlockLetter(letter)
        case "Swagman block":
            return SwagmanBlockLetter(letter)
        case "Bazeries block":
            return BazeriesBlockLetter(letter)
        case "Disrupted transposition block":
            return DisruptedBlockLetter(letter)
        case "Incomplete columnar block":
            return IncompleteColumnarBlockLetter(letter)
        case "Complete columnar block":
            return CompleteColumnarBlockLetter(letter)
        case "Alternating columnar block":
            return AlternatingColumnarBlockLetter(letter)
        case "Boustrophedon route block":
            return BoustrophedonRouteBlockLetter(letter)
        case "Spiral inward route block":
            return SpiralInwardRouteBlockLetter(letter)
        case "Spiral outward route block":
            return SpiralOutwardRouteBlockLetter(letter)
        case "Reading order route block":
            return ReadingOrderRouteBlockLetter(letter)
        case "Rotating square route block":
            return RotatingSquareRouteBlockLetter(letter)
        case "Grille mask block":
            return GrilleMaskBlockLetter(letter)
        case "Fleissner grille block":
            return FleissnerGrilleBlockLetter(letter)
        case "Homophonic substitution":
            return HomophonicSubstitutionLetter(letter)
        case "ADFGVX escaped":
            return ADFGVXEscapedLetter(letter)
        case "Base45 per letter":
            return Base45Letter(letter)
        case "Base36 per letter":
            return Base36Letter(letter)
        case "Base92 per letter":
            return Base92Letter(letter)
        case "Z85 per letter":
            return Z85Letter(letter)

        case "ROT47":
            return Rot47Letter(letter)
        case "Caesar custom alphabet":
            return CaesarCustomAlphabetLetter(letter)
        case "Della Porta disk":
            return DellaPortaDiskLetter(letter)
        case "Lorenz SZ40 toy stream":
            return LorenzToyStreamLetter(letter)
        case "Hagelin C-series toy stream":
            return HagelinToyStreamLetter(letter)
        case "Redefence rail offset block":
            return RedefenceBlockLetter(letter)
        case "Playfair Q omitted pairs":
            return PlayfairQOmittedLetter(letter)
        case "Double Playfair pairs":
            return DoublePlayfairLetter(letter)
        case "Twin Bifid pairs":
            return TwinBifidLetter(letter)
        case "Polybius columnar block":
            return PolybiusColumnarBlockLetter(letter)
        case "Base16 separated per letter":
            return Base16SeparatedLetter(letter)
        case "Base32Hex per letter":
            return Base32HexPerLetter(letter)
        case "Base64URL per letter":
            return Base64UrlPerLetter(letter)
        case "Base91 per letter":
            return Base91PerLetter(letter)
        case "RFC1924 Base85 per letter":
            return RFC1924Base85Letter(letter)
        case "yEnc per letter":
            return YEncLetter(letter)
        case "PEM armor token":
            return PEMArmorTokenLetter(letter)
        case "MessagePack hex token":
            return MessagePackHexTokenLetter(letter)
        case "Intel HEX record":
            return IntelHexRecordLetter(letter)
        case "Motorola S-record":
            return MotorolaSRecordLetter(letter)
        case "Cistercian numerals":
            return CistercianNumeralLetter(letter)
        case "Murray code":
            return MurrayCodeLetter(letter)
        case "APCO phonetic words":
            return APCOPhoneticLetter(letter)
        case "International signal phrases":
            return InternationalSignalPhraseLetter(letter)
        case "Younger Futhark runes":
            return YoungerFutharkLetter(letter)
        case "Cirth runes":
            return CirthRuneLetter(letter)
        case "Tengwar tokens":
            return TengwarTokenLetter(letter)
        case "Zodiac symbols":
            return ZodiacSymbolLetter(letter)
        case "Wingdings tokens":
            return WingdingsTokenLetter(letter)
        case "Braille grade 1":
            return BrailleGrade1Letter(letter)
        case "Bacon biliteral custom":
            return BaconBiliteralCustomLetter(letter)
        case "Solresol syllables":
            return SolresolLetter(letter)
        case "Music notes":
            return MusicNoteLetter(letter)
        case "Null acrostic words":
            return NullAcrosticWordLetter(letter)
        case "Acrostic cover words":
            return AcrosticCoverWordLetter(letter)
        case "Calculator spelling":
            return CalculatorSpellingLetter(letter)
        case "Vanity phone digits":
            return VanityPhoneDigitLetter(letter)
        case "Keyboard coordinates":
            return KeyboardCoordinateLetter(letter)
        case "QWERTY adjacent up":
            return QwertyAdjacentUpLetter(letter)
        case "QWERTY adjacent down":
            return QwertyAdjacentDownLetter(letter)
        case "Chessboard coordinates":
            return ChessboardCoordinateLetter(letter)
        case "Word Caesar":
            return WordCaesarLetter(letter)
        case "Backslang reverse":
            return BackslangLetter(letter)
        case "Pig Latin":
            return PigLatinLetter(letter)
        case "Rovarspraket":
            return RovarspraketLetter(letter)
        case "Tutnese token":
            return TutneseLetter(letter)
        case "Base3 per letter":
            return Base3Letter(letter)
        case "Base4 per letter":
            return Base4Letter(letter)
        case "Base8 per letter":
            return Base8Letter(letter)
        case "Base9 per letter":
            return Base9Letter(letter)
        case "Unary index":
            return UnaryIndexLetter(letter)
        case "Ternary index":
            return TernaryIndexLetter(letter)
        case "Balanced ternary index":
            return BalancedTernaryIndexLetter(letter)
        case "Hex color code":
            return HexColorLetter(letter)
        case "CSS hex escape":
            return CssHexEscapeLetter(letter)
        case "JavaScript hex escape":
            return JsHexEscapeLetter(letter)
        case "C string escape":
            return CStringEscapeLetter(letter)
        case "JSON string escape":
            return JSONStringEscapeLetter(letter)
        case "Octal escape token":
            return OctalEscapeTokenLetter(letter)
        case "Data URI token":
            return DataUriTokenLetter(letter)
        case "URL form token":
            return UrlFormTokenLetter(letter)
        case "Netstring token":
            return NetstringTokenLetter(letter)
        case "Bencode string token":
            return BencodeStringTokenLetter(letter)
        case "XXEncode per letter":
            return XXEncodePerLetter(letter)
        case "Gray code 8-bit":
            return GrayCode8Letter(letter)
        case "Parity bit token":
            return ParityBitTokenLetter(letter)
        case "Hamming 7,4 token":
            return Hamming74TokenLetter(letter)
        case "Hamming 15,11 token":
            return Hamming1511TokenLetter(letter)
        case "LEB128 token":
            return LEB128TokenLetter(letter)
        case "Elias gamma token":
            return EliasGammaTokenLetter(letter)
        case "Elias delta token":
            return EliasDeltaTokenLetter(letter)
        case "Fibonacci universal token":
            return FibonacciUniversalTokenLetter(letter)
        case "Golomb Rice token":
            return GolombRiceTokenLetter(letter)
        case "Luhn check token":
            return LuhnCheckTokenLetter(letter)
        case "Damm check token":
            return DammCheckTokenLetter(letter)
        case "CRC8 token":
            return CRC8TokenLetter(letter)
        case "CRC16 token":
            return CRC16TokenLetter(letter)
        case "CRC32 token":
            return CRC32TokenLetter(letter)
        case "Adler32 token":
            return Adler32TokenLetter(letter)
        case "Fletcher16 token":
            return Fletcher16TokenLetter(letter)
        case "RLE token":
            return RLETokenLetter(letter)
        case "Move-to-front index":
            return MoveToFrontIndexLetter(letter)
        case "Caesar box mini block":
            return CaesarBoxMiniBlockLetter(letter)
        case "Skip permutation block":
            return SkipPermutationBlockLetter(letter)
        case "Vertical transposition block":
            return VerticalTranspositionBlockLetter(letter)
        case "Rail fence spaces block":
            return RailFenceSpacesBlockLetter(letter)
        case "DNA triplet code":
            return DNATripletLetter(letter)
        case "RNA triplet code":
            return RNATripletLetter(letter)
        case "Protein name code":
            return ProteinNameCodeLetter(letter)
        case "Resistor color code":
            return ResistorColorCodeLetter(letter)
        case "Semaphore arms":
            return SemaphoreArmsLetter(letter)
        case "Keyed Caesar":
            return KeyedCaesarLetter(letter)
        case "Keyed progressive Caesar":
            return KeyedProgressiveCaesarLetter(letter)
        case "Interrupted key Vigenere":
            return InterruptedKeyVigenereLetter(letter)
        case "Progressive key Vigenere":
            return ProgressiveKeyVigenereLetter(letter)
        case "Variant Beaufort Autokey":
            return VariantBeaufortAutokeyLetter(letter)
        case "Running key book":
            return RunningKeyBookLetter(letter)
        case "Progressive Beaufort":
            return ProgressiveBeaufortLetter(letter)
        case "Progressive Variant Beaufort":
            return ProgressiveVariantBeaufortLetter(letter)
        case "Porta Autokey":
            return PortaAutokeyLetter(letter)
        case "Triangular Caesar shift":
            return TriangularCaesarShiftLetter(letter)
        case "Lucas Caesar shift":
            return LucasCaesarShiftLetter(letter)
        case "Square Caesar shift":
            return SquareCaesarShiftLetter(letter)
        case "Cube Caesar shift":
            return CubeCaesarShiftLetter(letter)
        case "Digital root Caesar shift":
            return DigitalRootCaesarShiftLetter(letter)
        case "Alternating Atbash":
            return AlternatingAtbashLetter(letter)
        case "Vigenere Atbash hybrid":
            return VigenereAtbashHybridLetter(letter)
        case "Polybius 0-based keyed":
            return Polybius0BasedKeyedLetter(letter)
        case "Polybius letter coords keyed":
            return PolybiusLetterCoordsKeyedLetter(letter)
        case "Grandpre coordinate":
            return GrandpreCoordinateLetter(letter)
        case "Fractionated Polybius token":
            return FractionatedPolybiusTokenLetter(letter)
        case "Base26 A0Z25":
            return Base26A0Z25Letter(letter)
        case "ASCII hex lowercase":
            return AsciiHexLowerLetter(letter)
        case "ASCII decimal padded":
            return AsciiDecimalPaddedLetter(letter)
        case "Binary ASCII 7-bit":
            return BinaryAscii7Letter(letter)
        case "Unicode decimal code point":
            return UnicodeDecimalCodePointLetter(letter)
        case "UTF-16BE hex":
            return Utf16BEHexLetter(letter)
        case "UTF-32BE hex":
            return Utf32BEHexLetter(letter)
        case "UTF-32LE hex":
            return Utf32LEHexLetter(letter)
        case "XML decimal entity":
            return XmlDecimalEntityLetter(letter)
        case "XML hex entity":
            return XmlHexEntityLetter(letter)
        case "Latin alphabet names":
            return LatinAlphabetNameLetter(letter)
        case "Greek alphabet names":
            return GreekAlphabetNameLetter(letter)
        case "Hebrew gematria":
            return HebrewGematriaLetter(letter)
        case "Greek isopsephy":
            return GreekIsopsephyLetter(letter)
        case "Scrabble values":
            return ScrabbleValueLetter(letter)
        case "Letter frequency rank":
            return LetterFrequencyRankLetter(letter)
        case "Periodic atomic numbers":
            return PeriodicAtomicNumberLetter(letter)
        case "Periodic element symbols":
            return PeriodicElementSymbolLetter(letter)
        case "NATO compact":
            return NatoCompactLetter(letter)
        case "LAPD phonetic words":
            return LapdPhoneticLetter(letter)
        case "RAF phonetic words":
            return RafPhoneticLetter(letter)
        case "Morse length code":
            return MorseLengthCodeLetter(letter)
        case "Morse dash count":
            return MorseDashCountLetter(letter)
        case "Morse dot count":
            return MorseDotCountLetter(letter)
        case "Flag token alphabet":
            return FlagTokenLetter(letter)
        case "Moon type tokens":
            return MoonTypeTokenLetter(letter)
        case "Theban tokens":
            return ThebanTokenLetter(letter)
        case "Dancing Men tokens":
            return DancingMenTokenLetter(letter)
        case "Standard Galactic tokens":
            return StandardGalacticTokenLetter(letter)
        case "Aurebesh tokens":
            return AurebeshTokenLetter(letter)
        case "Mathematical bold letters":
            return MathBoldLetter(letter)
        case "Mathematical italic letters":
            return MathItalicLetter(letter)
        case "Sans-serif letters":
            return SansSerifLetter(letter)
        case "Sans-serif bold letters":
            return SansSerifBoldLetter(letter)
        case "Monospace letters":
            return MonospaceLetter(letter)
        case "Negative circled letters":
            return NegativeCircledLetter(letter)
        case "Box drawing code":
            return BoxDrawingCodeLetter(letter)
        case "Geometric shape alphabet":
            return GeometricShapeLetter(letter)
        case "Vigenere keyed alphabet":
            return VigenereKeyedAlphabetLetter(letter)
        case "Beaufort keyed alphabet":
            return BeaufortKeyedAlphabetLetter(letter)
        case "Variant Beaufort keyed alphabet":
            return VariantBeaufortKeyedAlphabetLetter(letter)
        case "Autokey keyed alphabet":
            return AutokeyKeyedAlphabetLetter(letter)
        case "Porta numeric table":
            return PortaNumericTableLetter(letter)
        case "Porta reverse table":
            return PortaReverseTableLetter(letter)
        case "Atbash then Vigenere":
            return AtbashThenVigenereLetter(letter)
        case "Vigenere then Atbash":
            return VigenereThenAtbashLetter(letter)
        case "Running Atbash key":
            return RunningAtbashKeyLetter(letter)
        case "Autokey Atbash":
            return AutokeyAtbashLetter(letter)
        case "Progressive Affine":
            return ProgressiveAffineLetter(letter)
        case "Progressive Decimation":
            return ProgressiveDecimationLetter(letter)
        case "Multiplicative cipher x3":
            return MultiplicativeFixedLetter(letter, 3)
        case "Multiplicative cipher x5":
            return MultiplicativeFixedLetter(letter, 5)
        case "Multiplicative cipher x7":
            return MultiplicativeFixedLetter(letter, 7)
        case "Multiplicative cipher x11":
            return MultiplicativeFixedLetter(letter, 11)
        case "Multiplicative cipher x17":
            return MultiplicativeFixedLetter(letter, 17)
        case "Multiplicative cipher x25":
            return MultiplicativeFixedLetter(letter, 25)
        case "Baconian binary":
            return BaconianBinaryLetter(letter)
        case "Baconian reversed":
            return BaconianReversedLetter(letter)
        case "Baconian dots dashes":
            return BaconianDotsDashesLetter(letter)
        case "Baconian visible whitespace":
            return BaconianVisibleWhitespaceLetter(letter)
        case "Morse binary 10":
            return MorseBinary10Letter(letter)
        case "Morse binary 01":
            return MorseBinary01Letter(letter)
        case "Morse with slash":
            return MorseWithSlashLetter(letter)
        case "Morse compact digits":
            return MorseCompactDigitsLetter(letter)
        case "Morse decimal token":
            return MorseDecimalTokenLetter(letter)
        case "Morse hex token":
            return MorseHexTokenLetter(letter)
        case "Polybius 6x6":
            return Polybius6x6Letter(letter)
        case "ADFGVX 6x6 coords":
            return ADFGVX6x6CoordLetter(letter)
        case "Bifid numeric fraction":
            return BifidNumericFractionLetter(letter)
        case "Trifid numeric fraction":
            return TrifidNumericFractionLetter(letter)
        case "Nihilist plain coordinate":
            return NihilistPlainCoordinateLetter(letter)
        case "Checkerboard 6x6 coords":
            return Checkerboard6x6CoordLetter(letter)
        case "Base5 index":
            return BaseIndexLetter(letter, 5)
        case "Base6 index":
            return BaseIndexLetter(letter, 6)
        case "Base7 index":
            return BaseIndexLetter(letter, 7)
        case "Base11 index":
            return BaseIndexLetter(letter, 11)
        case "Base12 index":
            return BaseIndexLetter(letter, 12)
        case "Base16 index":
            return BaseIndexLetter(letter, 16)
        case "Base20 index":
            return BaseIndexLetter(letter, 20)
        case "QR alphanumeric index":
            return QRAlphanumericIndexLetter(letter)
        case "Code39 token":
            return Code39TokenLetter(letter)
        case "Codabar token":
            return CodabarTokenLetter(letter)
        case "Code128 token":
            return Code128TokenLetter(letter)
        case "ITF token":
            return ITFTokenLetter(letter)
        case "UPC-A check token":
            return UPCACheckTokenLetter(letter)
        case "EAN-13 check token":
            return EAN13CheckTokenLetter(letter)
        case "ISBN-10 check token":
            return ISBN10CheckTokenLetter(letter)
        case "ISBN-13 check token":
            return ISBN13CheckTokenLetter(letter)
        case "Mathematical double-struck":
            return MathDoubleStruckLetter(letter)
        case "Mathematical bold italic":
            return MathBoldItalicLetter(letter)
        case "Bold script letters":
            return MathBoldScriptLetter(letter)
        case "Bold fraktur letters":
            return MathBoldFrakturLetter(letter)
        case "Sans-serif italic letters":
            return SansSerifItalicLetter(letter)
        case "Sans-serif bold italic letters":
            return SansSerifBoldItalicLetter(letter)
        case "Greek actual letters":
            return GreekActualLetter(letter)
        case "Hebrew actual letters":
            return HebrewActualLetter(letter)
        case "Cyrillic actual letters":
            return CyrillicActualLetter(letter)
        case "Armenian actual letters":
            return ArmenianActualLetter(letter)
        case "Georgian actual letters":
            return GeorgianActualLetter(letter)
        case "Katakana phonetic":
            return KatakanaPhoneticLetter(letter)
        case "Latin reverse custom":
            return LatinReverseCustomLetter(letter)
        case "Headline puzzle words":
            return HeadlinePuzzleWordsLetter(letter)
        case "Dictionary code index":
            return DictionaryCodeIndexLetter(letter)
        case "Raster bits token":
            return RasterBitsTokenLetter(letter)
        case "Whitespace binary token":
            return WhitespaceBinaryTokenLetter(letter)
        case "Snow stego spaces token":
            return SnowStegoSpacesTokenLetter(letter)
        case "OpenPGP armor token":
            return OpenPGPArmorTokenLetter(letter)
        case "Base100 emoji byte":
            return Base100EmojiByteLetter(letter)
        case "Hexdump byte":
            return HexdumpByteLetter(letter)
        case "Binary endian word":
            return BinaryEndianWordLetter(letter)
        case "CRC64 token":
            return CRC64TokenLetter(letter)
        case "Fletcher32 token":
            return Fletcher32TokenLetter(letter)
        case "Verhoeff check token":
            return VerhoeffCheckTokenLetter(letter)
        case "MD5 toy token":
            return MD5ToyTokenLetter(letter)
        case "SHA1 toy token":
            return SHA1ToyTokenLetter(letter)
        case "SHA256 toy token":
            return SHA256ToyTokenLetter(letter)
        case "CRC16 CCITT token":
            return CRC16CCITTTokenLetter(letter)
        case "Punycode ascii token":
            return PunycodeAsciiTokenLetter(letter)
        case "Zero width binary visible":
            return ZeroWidthBinaryVisibleLetter(letter)
        case "Invisible unicode visible":
            return InvisibleUnicodeVisibleLetter(letter)
        case "ROT18 alpha":
            return ROT18AlphaLetter(letter)
        case "Knock code":
            return KnockCodeLetter(letter)
        case "Morse fractionated ADFGX":
            return MorseFractionatedADFGXLetter(letter)
        case "Morse syllable token":
            return MorseSyllableTokenLetter(letter)
        case "Gold-Bug cipher symbols":
            return GoldBugCipherSymbolLetter(letter)
        case "Rosicrucian cipher symbols":
            return RosicrucianSymbolLetter(letter)
        case "Templar cipher symbols":
            return TemplarSymbolLetter(letter)
        case "Malachim alphabet tokens":
            return MalachimTokenLetter(letter)
        case "Celestial alphabet tokens":
            return CelestialTokenLetter(letter)
        case "Enochian alphabet tokens":
            return EnochianTokenLetter(letter)
        case "Phoenician letters":
            return PhoenicianLetter(letter)
        case "Ugaritic cuneiform":
            return UgariticCuneiformLetter(letter)
        case "Etruscan tokens":
            return EtruscanTokenLetter(letter)
        case "Gothic letters":
            return GothicLetter(letter)
        case "Coptic letters":
            return CopticLetter(letter)
        case "Anglo-Saxon runes":
            return AngloSaxonRuneLetter(letter)
        case "Baudot tape holes":
            return BaudotTapeHolesLetter(letter)
        case "Murray punched tape":
            return MurrayPunchedTapeLetter(letter)
        case "Hollerith punch code":
            return HollerithPunchCodeLetter(letter)
        case "EBCDIC decimal":
            return EBCDICDecimalLetter(letter)
        case "IBM card row punch":
            return IBMCardRowPunchLetter(letter)
        case "Baconian slash":
            return BaconianSlashLetter(letter)
        case "Baconian high-low":
            return BaconianHighLowLetter(letter)
        case "Polybius checker A-E":
            return PolybiusCheckerAELetter(letter)
        case "Polybius checker 0-4":
            return PolybiusChecker04Letter(letter)
        case "Tap code knocks":
            return TapCodeKnocksLetter(letter)
        case "Prison tap code":
            return PrisonTapCodeLetter(letter)
        case "Fractionated tap code":
            return FractionatedTapCodeLetter(letter)
        case "Bifid coordinate stream":
            return BifidCoordinateStreamLetter(letter)
        case "Trifid coordinate stream":
            return TrifidCoordinateStreamLetter(letter)
        case "Nihilist plus key stream":
            return NihilistPlusKeyStreamLetter(letter)
        case "Hill coordinate token":
            return HillCoordinateTokenLetter(letter)
        case "Modular inverse index":
            return ModularInverseIndexLetter(letter)
        case "Affine family token":
            return AffineFamilyTokenLetter(letter)
        case "OTP numeric token":
            return OTPNumericTokenLetter(letter)
        case "Vernam bitmask token":
            return VernamBitmaskTokenLetter(letter)
        case "RC4 keystream token":
            return RC4KeystreamTokenLetter(letter)
        case "ChaCha toy token":
            return ChaChaToyTokenLetter(letter)
        case "Salsa toy token":
            return SalsaToyTokenLetter(letter)
        case "Z85 index":
            return Z85IndexLetter(letter)
        case "Bech32 index":
            return Bech32IndexLetter(letter)
        case "z-base-32 index":
            return ZBase32IndexLetter(letter)
        case "Crockford byte token":
            return CrockfordByteTokenLetter(letter)
        case "Caesar reverse alphabet shift":
            return V20ExtraLetter(letter, "Caesar reverse alphabet shift")
        case "Atbash Caesar shift":
            return V20ExtraLetter(letter, "Atbash Caesar shift")
        case "ROT13 then Atbash":
            return V20ExtraLetter(letter, "ROT13 then Atbash")
        case "Vigenere reversed alphabet":
            return V20ExtraLetter(letter, "Vigenere reversed alphabet")
        case "Beaufort reversed alphabet":
            return V20ExtraLetter(letter, "Beaufort reversed alphabet")
        case "Gronsfeld reversed alphabet":
            return V20ExtraLetter(letter, "Gronsfeld reversed alphabet")
        case "Autokey reversed alphabet":
            return V20ExtraLetter(letter, "Autokey reversed alphabet")
        case "Progressive key Beaufort":
            return V20ExtraLetter(letter, "Progressive key Beaufort")
        case "Interrupted Beaufort":
            return V20ExtraLetter(letter, "Interrupted Beaufort")
        case "Keyed Beaufort":
            return V20ExtraLetter(letter, "Keyed Beaufort")
        case "Keyed Variant Beaufort":
            return V20ExtraLetter(letter, "Keyed Variant Beaufort")
        case "Slide Vigenere":
            return V20ExtraLetter(letter, "Slide Vigenere")
        case "Diana reciprocal":
            return V20ExtraLetter(letter, "Diana reciprocal")
        case "Vigenere Fibonacci stream":
            return V20ExtraLetter(letter, "Vigenere Fibonacci stream")
        case "Vigenere Lucas stream":
            return V20ExtraLetter(letter, "Vigenere Lucas stream")
        case "Vigenere prime stream":
            return V20ExtraLetter(letter, "Vigenere prime stream")
        case "Vigenere triangular stream":
            return V20ExtraLetter(letter, "Vigenere triangular stream")
        case "Multiplicative progressive":
            return V20ExtraLetter(letter, "Multiplicative progressive")
        case "Affine with key shift":
            return V20ExtraLetter(letter, "Affine with key shift")
        case "Caesar keyed stream":
            return V20ExtraLetter(letter, "Caesar keyed stream")
        case "Porta progressive reverse":
            return V20ExtraLetter(letter, "Porta progressive reverse")
        case "Trithemius descending":
            return V20ExtraLetter(letter, "Trithemius descending")
        case "Polybius row letters":
            return V20ExtraLetter(letter, "Polybius row letters")
        case "Polybius column letters":
            return V20ExtraLetter(letter, "Polybius column letters")
        case "Polybius chess coords":
            return V20ExtraLetter(letter, "Polybius chess coords")
        case "Polybius barcode token":
            return V20ExtraLetter(letter, "Polybius barcode token")
        case "Polybius binary coords":
            return V20ExtraLetter(letter, "Polybius binary coords")
        case "Bifid raw coords":
            return V20ExtraLetter(letter, "Bifid raw coords")
        case "Trifid raw coords":
            return V20ExtraLetter(letter, "Trifid raw coords")
        case "ADFGX spaced":
            return V20ExtraLetter(letter, "ADFGX spaced")
        case "ADFGVX spaced":
            return V20ExtraLetter(letter, "ADFGVX spaced")
        case "Nihilist keyed number":
            return V20ExtraLetter(letter, "Nihilist keyed number")
        case "Checkerboard serial":
            return V20ExtraLetter(letter, "Checkerboard serial")
        case "Tap binary token":
            return V20ExtraLetter(letter, "Tap binary token")
        case "Knock binary token":
            return V20ExtraLetter(letter, "Knock binary token")
        case "Baconian 12345":
            return V20ExtraLetter(letter, "Baconian 12345")
        case "Baconian emoji":
            return V20ExtraLetter(letter, "Baconian emoji")
        case "Baconian morse":
            return V20ExtraLetter(letter, "Baconian morse")
        case "Baconian Roman":
            return V20ExtraLetter(letter, "Baconian Roman")
        case "LCG stream hex":
            return V20ExtraLetter(letter, "LCG stream hex")
        case "Xorshift stream hex":
            return V20ExtraLetter(letter, "Xorshift stream hex")
        case "Blum Blum Shub toy":
            return V20ExtraLetter(letter, "Blum Blum Shub toy")
        case "Fibonacci LFSR toy":
            return V20ExtraLetter(letter, "Fibonacci LFSR toy")
        case "Vernam decimal byte":
            return V20ExtraLetter(letter, "Vernam decimal byte")
        case "OTP base26 token":
            return V20ExtraLetter(letter, "OTP base26 token")
        case "Running key numeric":
            return V20ExtraLetter(letter, "Running key numeric")
        case "Base24 index":
            return V20ExtraLetter(letter, "Base24 index")
        case "Base30 index":
            return V20ExtraLetter(letter, "Base30 index")
        case "Base64 index":
            return V20ExtraLetter(letter, "Base64 index")
        case "Base85 index":
            return V20ExtraLetter(letter, "Base85 index")
        case "ASCII base3 byte":
            return V20ExtraLetter(letter, "ASCII base3 byte")
        case "ASCII base4 byte":
            return V20ExtraLetter(letter, "ASCII base4 byte")
        case "ASCII base5 byte":
            return V20ExtraLetter(letter, "ASCII base5 byte")
        case "ASCII base6 byte":
            return V20ExtraLetter(letter, "ASCII base6 byte")
        case "ASCII base12 byte":
            return V20ExtraLetter(letter, "ASCII base12 byte")
        case "ASCII base36 byte":
            return V20ExtraLetter(letter, "ASCII base36 byte")
        case "UTF-8 bytes decimal":
            return V20ExtraLetter(letter, "UTF-8 bytes decimal")
        case "UTF-8 bytes hex spaced":
            return V20ExtraLetter(letter, "UTF-8 bytes hex spaced")
        case "Java unicode escape":
            return V20ExtraLetter(letter, "Java unicode escape")
        case "Python unicode escape":
            return V20ExtraLetter(letter, "Python unicode escape")
        case "CSharp unicode escape":
            return V20ExtraLetter(letter, "CSharp unicode escape")
        case "CSS unicode padded":
            return V20ExtraLetter(letter, "CSS unicode padded")
        case "SQL CHAR token":
            return V20ExtraLetter(letter, "SQL CHAR token")
        case "PowerShell char token":
            return V20ExtraLetter(letter, "PowerShell char token")
        case "Decimal entity padded":
            return V20ExtraLetter(letter, "Decimal entity padded")
        case "Hex entity padded":
            return V20ExtraLetter(letter, "Hex entity padded")
        case "Percent lowercase":
            return V20ExtraLetter(letter, "Percent lowercase")
        case "Percent uppercase spaced":
            return V20ExtraLetter(letter, "Percent uppercase spaced")
        case "Quoted printable soft token":
            return V20ExtraLetter(letter, "Quoted printable soft token")
        case "Morse prosign token":
            return V20ExtraLetter(letter, "Morse prosign token")
        case "NATO initials only":
            return V20ExtraLetter(letter, "NATO initials only")
        case "Pigpen grid code":
            return V20ExtraLetter(letter, "Pigpen grid code")
        case "Templar cross code":
            return V20ExtraLetter(letter, "Templar cross code")
        case "Semaphore compass":
            return V20ExtraLetter(letter, "Semaphore compass")
        case "Braille dots token":
            return V20ExtraLetter(letter, "Braille dots token")
        case "Moon phase alphabet":
            return V20ExtraLetter(letter, "Moon phase alphabet")
        case "Planet sequence alphabet":
            return V20ExtraLetter(letter, "Planet sequence alphabet")
        case "Diceware coordinate token":
            return V20ExtraLetter(letter, "Diceware coordinate token")
        case "Reciprocal Vigenere", "Reciprocal Gronsfeld", "Beaufort Fibonacci stream", "Beaufort prime stream", "Variant Beaufort Fibonacci", "Variant Beaufort prime", "Autokey Caesar stream", "Progressive Atbash stream", "Keyed Polybius 0-4", "Keyed Polybius A-E", "Keyed Tap coordinate", "ADFGX numeric labels", "ADFGVX numeric labels", "Polybius mixed 6x6 keyed", "Checkerboard 10x10 token", "VIC chain addition toy", "Nihilist zero padded", "Nihilist keyed hex", "Bifid split token", "Trifid layer token":
            return V21ExtraLetter(letter, modeName)
        case "Playfair digraph marker", "Hill mod26 vector token", "Modular square index", "Modular cube index", "Power residue index", "Quadratic residue token", "QR format bits token", "Aztec barcode token", "PDF417 codeword token", "DataMatrix codeword token", "Code93 token", "MSI check token", "Interleaved 2 of 5 pair", "POSTNET digit token", "PLANET digit token", "Royal Mail 4-state token", "KIX 4-state token", "Facing identification mark", "OCR-A token", "MICR E13B token":
            return V21ExtraLetter(letter, modeName)
        case "MIME quoted word Q", "MIME quoted word B", "LDAP hex escape", "Regex unicode escape", "XML CDATA token", "CSV quoted token", "Shell ANSI C escape", "Bash hex token", "Python bytes token", "Ruby hex token", "Perl hex token", "Go rune token", "Rust unicode token", "HTML named fallback", "SGML entity token", "TeX char token", "PostScript char token", "Assembly DB hex", "Intel asm char", "MIPS ascii byte":
            return V21ExtraLetter(letter, modeName)
        case "Byte pair hex token", "Nibble swap hex", "Bit reverse byte", "Gray code reflected", "Excess-3 BCD token", "BCD 2421 token", "BCD 5211 token", "Johnson code token", "One-hot index token", "Two-hot index token", "Huffman toy token", "Shannon-Fano toy token", "Morse American token", "Chappe semaphore token", "Optical telegraph token", "Navajo code talker token", "Commercial code word", "Telegraph code word", "Postal abbreviation token", "Weather code token":
            return V21ExtraLetter(letter, modeName)
        case "Vigenere minus key", "Vigenere plus Atbash", "Beaufort Atbash hybrid", "Variant Beaufort Atbash hybrid", "Caesar sine wave shift", "Caesar cosine wave shift", "Caesar sawtooth shift", "Caesar square wave shift", "Caesar triangular wave shift", "Prime gap Caesar shift", "Pell Caesar shift", "Jacobsthal Caesar shift", "Padovan Caesar shift", "Tetranacci Caesar shift", "Keyed reciprocal substitution", "Keyed reverse substitution", "Keyword transposed alphabet", "Alphabet rail split", "Alphabet odd-even split", "Alphabet vowel-first":
            return V22ExtraLetter(letter, modeName)
        case "Alphabet consonant-first", "Alphabet frequency order", "Polybius Greek labels", "Polybius Morse labels", "Polybius Roman labels", "Polybius symbol coords", "Polybius NATO coords", "Checkerboard phone coords", "Checkerboard keyboard coords", "Checkerboard hex coords", "ADFGX reversed square", "ADFGVX reversed square", "Baconian Greek", "Baconian binary spaced", "Baconian quinary digits", "Baconian 0-1 compact", "Baconian braille", "Baconian flag token", "Morse Unicode symbols", "Morse blocks":
            return V22ExtraLetter(letter, modeName)
        case "Morse arrows", "Morse vowels consonants", "Morse word code", "Morse phone taps", "Morse base3 token", "Morse length-dash-dot", "ASCII base13 byte", "ASCII base17 byte", "ASCII base19 byte", "ASCII base21 byte", "ASCII base23 byte", "ASCII base27 byte", "ASCII base31 byte", "ASCII base52 byte", "UTF-8 binary compact", "UTF-8 hex colon", "UTF-16BE decimal", "UTF-32LE decimal", "URI component token", "CSS escape short":
            return V22ExtraLetter(letter, modeName)
        case "HTML entity hex padded", "XML entity decimal padded", "Base64 no padding per letter", "Base32 no padding per letter", "Base85 ascii85 framed", "Base91 index token", "CRC4 token", "CRC5 USB token", "CRC6 token", "CRC7 token", "CRC12 token", "CRC24 toy token", "LRC token", "XOR checksum token", "EAN-8 check token", "Code11 check token", "Pharmacode token", "Telepen token", "Maxicode word token", "QR byte mode token":
            return V22ExtraLetter(letter, modeName)
        case "DataMatrix ASCII token", "Aztec compact word token", "RTTY mark-space token", "Baudot reversed bits", "ITA2 letters only token", "Varicode token", "Hellschreiber token", "AX25 callsign token", "AIS six-bit token", "Murray reversed bits", "Glagolitic letters", "Old Turkic runes", "Avestan letters", "Linear B tokens", "Egyptian alphabet tokens", "Mayan bar-dot token", "Kaktovik numeral token", "Greek acrophonic token", "Factoradic index", "Cantor pairing token":
            return V22ExtraLetter(letter, modeName)
        case "Godel prime token", "Lehmer code token", "Catalan number token", "Bell number token", "Happy number token", "Perfect square marker":
            return V22ExtraLetter(letter, modeName)
        case "Keyed alphabet Caesar":
            return V23ExtraLetter(letter, modeName)
        case "Caesar Catalan shift", "Caesar Bell shift", "Caesar Perrin shift", "Caesar Motzkin shift", "Caesar Collatz shift", "Vigenere square stream", "Vigenere cube stream", "Vigenere Catalan stream", "Vigenere prime-gap stream", "Beaufort triangular stream", "Beaufort square stream", "Variant Beaufort Lucas stream", "Autokey Gronsfeld", "Running key Beaufort", "Progressive ROT47 printable", "Printable ASCII Caesar", "Printable ASCII Atbash", "Printable Vigenere", "Printable Beaufort", "Keyed alphabet Caesar +13":
            return V23ExtraLetter(letter, modeName)
        case "Keyed alphabet reciprocal", "Mixed alphabet ROT13", "Frequency keyed substitution", "Dvorak to QWERTY", "AZERTY to QWERTY", "Colemak to QWERTY", "QWERTY row rotate", "Keyboard column code", "Keyboard diagonal code", "Morse star bar", "Morse bullet dash", "Morse pulse widths", "Morse timed token", "Morse Japanese Wabun token", "Baconian lowercase uppercase":
            return V23ExtraLetter(letter, modeName)
        case "Baconian chess pieces", "Baconian dice faces", "Baconian roman binary", "Baconian hexadecimal", "Polybius 7x4", "Polybius 4x7", "Polybius 13x2", "Polybius zodiac labels", "Polybius planet labels", "ADFGX Morse square", "ADFGVX phone square", "Tap code 0-based", "Tap code row-column words", "Nihilist product token", "Hill 2x2 coordinate token", "Hill 3x3 coordinate token", "Affine modulo 29 token", "Affine modulo 31 token", "Affine modulo 37 token", "Zeckendorf index":
            return V23ExtraLetter(letter, modeName)
        case "Elias omega token", "Rice unary-binary token", "Balanced quinary index", "Balanced senary index", "Prime product index", "Chinese remainder token", "Residue vector mod 2-3-5", "Fibonacci word token", "Thue-Morse token", "ASCII base14 byte", "ASCII base15 byte", "ASCII base18 byte", "ASCII base22 byte", "ASCII base25 byte", "ASCII base28 byte":
            return V23ExtraLetter(letter, modeName)
        case "ASCII base29 byte", "ASCII base33 byte", "ASCII base34 byte", "ASCII base35 byte", "UTF-8 C array token", "UUID byte token", "GUID byte token", "IPv4 octet token", "IPv6 hextet token", "DNS label token", "INI hex token", "TOML unicode token", "YAML unicode token", "CSV hex cell token", "QR numeric token", "GS1 AI token", "Aztec binary token", "PDF417 compact token", "DataMatrix C40 token", "Cherokee letters":
            return V23ExtraLetter(letter, modeName)
        case "Canadian syllabics", "Hiragana phonetic", "Hangul jamo token", "Thai alphabet token", "Devanagari letters", "Bengali letters", "Arabic abjad", "Syriac letters", "Tifinagh letters", "Samaritan letters", "Nabataean tokens", "Pahlavi tokens", "Old Persian cuneiform", "Cypriot syllabary tokens", "Huffman fixed token":
            return V23ExtraLetter(letter, modeName)
        case "LZW dictionary token", "BWT rotation token", "Arithmetic toy interval", "Range coder toy token", "Deflate block marker", "Brotli meta token", "Zstd sequence token", "RLE binary run token", "Move-to-front rank token":
            return V23ExtraLetter(letter, modeName)
        case "Vigenere Pell stream", "Vigenere Jacobsthal stream", "Vigenere Padovan stream", "Vigenere Tetranacci stream", "Beaufort Catalan stream", "Beaufort Bell stream", "Variant Beaufort Pell stream", "Variant Beaufort Jacobsthal stream", "Porta Fibonacci stream", "Porta prime-gap stream", "Caesar Perrin stream", "Caesar Motzkin stream", "Caesar Thue-Morse stream", "Caesar Golomb stream", "Caesar bitcount stream", "Caesar digital-sum stream", "Caesar modular inverse stream", "Caesar quadratic residue stream", "Caesar power-of-two stream", "Caesar factorial mod shift":
            return V27ExtraLetter(letter, modeName)
        case "Keyed alphabet Fibonacci", "Keyed alphabet prime", "Keyed alphabet triangular", "Reverse-keyword substitution", "Beaufort reciprocal alphabet", "Vigenere reciprocal alphabet", "Nihilist mod 100 token", "Nihilist hex stream token", "Polybius row-major binary", "Polybius column-major binary", "Polybius knight coords", "Polybius spiral coords", "Checkerboard Morse rows", "Checkerboard NATO columns", "Tap code Morse token", "Tap code binary token v2", "Fractionated Morse numeric", "Fractionated Morse base3", "Pollux binary 0-1-2", "Pollux emoji 0-1-2":
            return V27ExtraLetter(letter, modeName)
        case "Morbit binary pairs", "Morbit ternary pairs", "Baconian Baudot", "Baconian five-bit binary", "Baconian quaternary tag", "A1Z26 mod 9", "A1Z26 mod 11", "A1Z26 Roman lowercase", "A1Z26 Greek numerals", "A1Z26 resistor colors", "ASCII base37 byte", "ASCII base38 byte", "ASCII base39 byte", "ASCII base40 byte", "ASCII base41 byte", "ASCII base42 byte", "ASCII base43 byte", "ASCII base44 byte", "UTF-8 octets bracketed", "UTF-16LE bytes bracketed":
            return V27ExtraLetter(letter, modeName)
        case "Unicode plane token", "HTML named alpha token", "TeX alphabet command", "LaTeX mathbb command", "LaTeX mathcal command", "PostScript glyph name", "QR alphanumeric value", "Base45 byte token", "Base58 byte token", "Base91 byte token", "Reed-Solomon toy syndrome", "Hamming parity syndrome", "BCH toy syndrome", "ISBN letter checksum", "EAN letter checksum", "Codabar alphabet token", "Code39 full ASCII token", "Teleprinter shift token", "SITOR bit token", "Baudot Murray token compact":
            return V27ExtraLetter(letter, modeName)
        case "NATO words":
            return NatoLetter(letter)
    }
    return letter
}


; ------------------------------------------------------------
; v13 additional live ciphers / encodings
; ------------------------------------------------------------

WordCaesarLetter(letter) {
    global shiftValue
    ; Per-letter live adaptation: shift within alphabet by the configured word shift.
    return ShiftLetter(letter, shiftValue)
}

BackslangLetter(letter) {
    ; A single live letter cannot reverse a whole message, so this mirrors the alphabet.
    return AtbashLetter(letter)
}

PigLatinLetter(letter) {
    u := StrUpper(letter)
    if InStr("AEIOU", u)
        out := u . "WAY"
    else
        out := "-" . u . "AY"
    return IsUpperLetter(letter) ? out : StrLower(out)
}

RovarspraketLetter(letter) {
    u := StrUpper(letter)
    if InStr("AEIOUY", u)
        return letter
    out := u . "O" . u
    return IsUpperLetter(letter) ? out : StrLower(out)
}

TutneseLetter(letter) {
    u := StrUpper(letter)
    idx := LetterIndex(u) + 1
    words := StrSplit("ayay|bub|cash|dud|eyay|fuf|gug|hash|iyay|jug|kuck|lul|mum|nun|oyay|pup|quack|rur|sus|tut|uyay|vuv|wack|ex|yub|zub", "|")
    out := (idx >= 1 && idx <= words.Length) ? words[idx] : letter
    return IsUpperLetter(letter) ? StrUpper(SubStr(out,1,1)) . SubStr(out,2) : out
}

BaseN(value, base) {
    digits := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    value := Integer(value)
    if value = 0
        return "0"
    out := ""
    while value > 0 {
        rem := Mod(value, base)
        out := SubStr(digits, rem + 1, 1) . out
        value := Floor(value / base)
    }
    return out
}

Base3Letter(letter) {
    return BaseN(Ord(letter), 3) . " "
}

Base4Letter(letter) {
    return BaseN(Ord(letter), 4) . " "
}

Base8Letter(letter) {
    return BaseN(Ord(letter), 8) . " "
}

Base9Letter(letter) {
    return BaseN(Ord(letter), 9) . " "
}

UnaryIndexLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return RepeatChar("1", n) . "0 "
}

TernaryIndexLetter(letter) {
    return BaseN(LetterIndex(StrUpper(letter)) + 1, 3) . " "
}

BalancedTernaryIndexLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    if n = 0
        return "0 "
    out := ""
    while n != 0 {
        r := Mod(n, 3)
        n := Floor(n / 3)
        if r = 2 {
            r := -1
            n += 1
        }
        out := (r = -1 ? "T" : r) . out
    }
    return out . " "
}

HexColorLetter(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    r := Mod(idx * 47, 256), g := Mod(idx * 91, 256), b := Mod(idx * 137, 256)
    return Format("#{:02X}{:02X}{:02X} ", r, g, b)
}

CssHexEscapeLetter(letter) {
    return Format("\\{:X} ", Ord(letter))
}

JsHexEscapeLetter(letter) {
    return Format("\\x{:02X}", Ord(letter))
}

CStringEscapeLetter(letter) {
    return Format("\\x{:02X}", Ord(letter))
}

JSONStringEscapeLetter(letter) {
    return Format("\\u{:04X}", Ord(letter))
}

OctalEscapeTokenLetter(letter) {
    return "\\" . Format("{:03o}", Ord(letter))
}

DataUriTokenLetter(letter) {
    return "data:text/plain,%" . Format("{:02X}", Ord(letter)) . " "
}

UrlFormTokenLetter(letter) {
    return "%" . Format("{:02X}", Ord(letter))
}

NetstringTokenLetter(letter) {
    return "1:" . letter . ","
}

BencodeStringTokenLetter(letter) {
    return "1:" . letter
}

XXEncodePerLetter(letter) {
    alph := "+-0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    b := Ord(letter)
    c1 := (b >> 2) & 63
    c2 := (b & 3) << 4
    return SubStr(alph, c1 + 1, 1) . SubStr(alph, c2 + 1, 1) . "== "
}

ByteBits(n) {
    out := ""
    Loop 8
        out := ((n >> (A_Index - 1)) & 1) . out
    return out
}

GrayCode8Letter(letter) {
    b := Ord(letter)
    g := b ^ (b >> 1)
    return ByteBits(g) . " "
}

ParityBitTokenLetter(letter) {
    b := Ord(letter)
    ones := 0
    Loop 8
        ones += (b >> (A_Index - 1)) & 1
    return ByteBits(b) . Mod(ones, 2) . " "
}

Hamming74Nibble(n) {
    d1 := (n >> 3) & 1, d2 := (n >> 2) & 1, d3 := (n >> 1) & 1, d4 := n & 1
    p1 := d1 ^ d2 ^ d4
    p2 := d1 ^ d3 ^ d4
    p3 := d2 ^ d3 ^ d4
    return "" . p1 . p2 . d1 . p3 . d2 . d3 . d4
}

Hamming74TokenLetter(letter) {
    b := Ord(letter)
    return Hamming74Nibble((b >> 4) & 15) . " " . Hamming74Nibble(b & 15) . " "
}

Hamming1511TokenLetter(letter) {
    b := Ord(letter)
    ; Compact live token: 8 data bits plus 4 parity/check bits and 3 zero fill bits.
    p1 := ((b>>0)&1) ^ ((b>>1)&1) ^ ((b>>3)&1) ^ ((b>>4)&1) ^ ((b>>6)&1)
    p2 := ((b>>0)&1) ^ ((b>>2)&1) ^ ((b>>3)&1) ^ ((b>>5)&1) ^ ((b>>6)&1)
    p4 := ((b>>1)&1) ^ ((b>>2)&1) ^ ((b>>3)&1) ^ ((b>>7)&1)
    p8 := ((b>>4)&1) ^ ((b>>5)&1) ^ ((b>>6)&1) ^ ((b>>7)&1)
    return ByteBits(b) . p1 . p2 . p4 . p8 . "000 "
}

LEB128TokenLetter(letter) {
    n := Ord(letter)
    out := ""
    loop {
        byte := n & 0x7F
        n := n >> 7
        if n != 0
            byte := byte | 0x80
        out .= Format("{:02X}", byte)
        if n = 0
            break
    }
    return out . " "
}

EliasGammaTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    bin := BaseN(n, 2)
    return RepeatChar("0", StrLen(bin) - 1) . bin . " "
}

EliasDeltaTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    bin := BaseN(n, 2)
    L := StrLen(bin)
    gammaL := RepeatChar("0", StrLen(BaseN(L, 2)) - 1) . BaseN(L, 2)
    return gammaL . SubStr(bin, 2) . " "
}

FibonacciUniversalTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    fib := [1,2]
    while fib[fib.Length] <= n
        fib.Push(fib[fib.Length] + fib[fib.Length - 1])
    out := ""
    rem := n
    Loop fib.Length - 1 {
        i := fib.Length - A_Index
        if fib[i] <= rem {
            out := "1" . out
            rem -= fib[i]
        } else {
            out := "0" . out
        }
    }
    return out . "1 "
}

GolombRiceTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter))
    m := 4
    q := Floor(n / m)
    r := Mod(n, m)
    return RepeatChar("1", q) . "0" . Format("{:02b}", r) . " "
}

LuhnCheckDigit(n) {
    s := (n . "")
    sum := 0
    dbl := true
    i := StrLen(s)
    while i >= 1 {
        d := Integer(SubStr(s, i, 1))
        if dbl {
            d *= 2
            if d > 9
                d -= 9
        }
        sum += d
        dbl := !dbl
        i -= 1
    }
    return Mod(10 - Mod(sum, 10), 10)
}

LuhnCheckTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return Format("{:02d}{} ", n, LuhnCheckDigit(n))
}

DammCheckTokenLetter(letter) {
    static table := [[0,3,1,7,5,9,8,6,4,2],[7,0,9,2,1,5,4,8,6,3],[4,2,0,6,8,7,1,3,5,9],[1,7,5,0,9,8,3,4,2,6],[6,1,2,3,0,4,5,9,7,8],[3,6,7,4,2,0,9,5,8,1],[5,8,6,9,7,2,0,1,3,4],[8,9,4,5,3,6,2,0,1,7],[9,4,3,8,6,1,7,2,0,5],[2,5,8,1,4,3,6,7,9,0]]
    n := Format("{:02d}", LetterIndex(StrUpper(letter)) + 1)
    interim := 0
    for _, ch in StrSplit(n)
        interim := table[interim + 1][Integer(ch) + 1]
    return n . interim . " "
}

CRC8TokenLetter(letter) {
    crc := Ord(letter)
    Loop 8 {
        if (crc & 0x80)
            crc := ((crc << 1) ^ 0x07) & 0xFF
        else
            crc := (crc << 1) & 0xFF
    }
    return Format("{:02X} ", crc)
}

CRC16TokenLetter(letter) {
    crc := 0xFFFF ^ (Ord(letter) << 8)
    Loop 8 {
        if (crc & 0x8000)
            crc := ((crc << 1) ^ 0x1021) & 0xFFFF
        else
            crc := (crc << 1) & 0xFFFF
    }
    return Format("{:04X} ", crc)
}

CRC32TokenLetter(letter) {
    crc := 0xFFFFFFFF ^ Ord(letter)
    Loop 8 {
        if (crc & 1)
            crc := (crc >> 1) ^ 0xEDB88320
        else
            crc := crc >> 1
    }
    crc := crc ^ 0xFFFFFFFF
    return Format("{:08X} ", crc & 0xFFFFFFFF)
}

Adler32TokenLetter(letter) {
    a := 1 + Ord(letter)
    b := a
    return Format("{:08X} ", ((b & 0xFFFF) << 16) | (a & 0xFFFF))
}

Fletcher16TokenLetter(letter) {
    a := Mod(Ord(letter), 255)
    b := a
    return Format("{:04X} ", (b << 8) | a)
}

RLETokenLetter(letter) {
    return "1" . letter . " "
}

MoveToFrontIndexLetter(letter) {
    global ALPHABET
    static alphabetState := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    u := StrUpper(letter)
    idx := InStr(alphabetState, u)
    if idx <= 0
        return letter
    alphabetState := u . StrReplace(alphabetState, u)
    return idx - 1 . " "
}

BufferBlockLetter(letter, size, transformName) {
    global pairBuffer
    pairBuffer .= StrUpper(letter)
    if StrLen(pairBuffer) < size
        return ""
    block := pairBuffer
    pairBuffer := ""
    return TransformMiniBlock(block, transformName) . " "
}

CaesarBoxMiniBlockLetter(letter) {
    return BufferBlockLetter(letter, 9, "CaesarBox")
}

SkipPermutationBlockLetter(letter) {
    return BufferBlockLetter(letter, 8, "SkipPermutation")
}

VerticalTranspositionBlockLetter(letter) {
    return BufferBlockLetter(letter, 8, "VerticalTransposition")
}

RailFenceSpacesBlockLetter(letter) {
    return BufferBlockLetter(letter, 8, "RailFenceSpaces")
}

TransformMiniBlock(block, name) {
    if name = "CaesarBox" {
        ; 3x3: read down columns.
        return SubStr(block,1,1) . SubStr(block,4,1) . SubStr(block,7,1) . SubStr(block,2,1) . SubStr(block,5,1) . SubStr(block,8,1) . SubStr(block,3,1) . SubStr(block,6,1) . SubStr(block,9,1)
    }
    if name = "SkipPermutation" {
        return SubStr(block,1,1) . SubStr(block,3,1) . SubStr(block,5,1) . SubStr(block,7,1) . SubStr(block,2,1) . SubStr(block,4,1) . SubStr(block,6,1) . SubStr(block,8,1)
    }
    if name = "VerticalTransposition" {
        return SubStr(block,1,1) . SubStr(block,5,1) . SubStr(block,2,1) . SubStr(block,6,1) . SubStr(block,3,1) . SubStr(block,7,1) . SubStr(block,4,1) . SubStr(block,8,1)
    }
    if name = "RailFenceSpaces" {
        return SubStr(block,1,1) . SubStr(block,3,1) . SubStr(block,5,1) . SubStr(block,7,1) . SubStr(block,2,1) . SubStr(block,4,1) . SubStr(block,6,1) . SubStr(block,8,1)
    }
    return block
}

DNATripletLetter(letter) {
    static codons := ["GCT","GCC","GCA","GCG","CGT","CGC","CGA","CGG","AAT","AAC","GAT","GAC","TGT","TGC","CAA","CAG","GAA","GAG","GGT","GGC","GGA","GGG","CAT","CAC","ATT","ATC"]
    return codons[LetterIndex(StrUpper(letter)) + 1] . " "
}

RNATripletLetter(letter) {
    return StrReplace(DNATripletLetter(letter), "T", "U")
}

ProteinNameCodeLetter(letter) {
    static names := ["Alanine","Arginine","Asparagine","Aspartic-acid","Cysteine","Glutamine","Glutamic-acid","Glycine","Histidine","Isoleucine","Leucine","Lysine","Methionine","Phenylalanine","Proline","Serine","Threonine","Tryptophan","Tyrosine","Valine","Sec","Pyl","Asx","Glx","Xle","Stop"]
    return names[LetterIndex(StrUpper(letter)) + 1] . " "
}

ResistorColorCodeLetter(letter) {
    static colors := ["black","brown","red","orange","yellow","green","blue","violet","gray","white"]
    n := LetterIndex(StrUpper(letter)) + 1
    tens := Floor(n / 10)
    ones := Mod(n, 10)
    return colors[tens + 1] . "-" . colors[ones + 1] . " "
}

SemaphoreArmsLetter(letter) {
    static pairs := ["1-2","1-3","1-4","1-5","1-6","1-7","1-8","2-3","2-4","2-5","2-6","2-7","2-8","3-4","3-5","3-6","3-7","3-8","4-5","4-6","4-7","4-8","5-6","5-7","5-8","6-7"]
    return pairs[LetterIndex(StrUpper(letter)) + 1] . " "
}

; ------------------------------------------------------------
; Enigma M3/M4
; ------------------------------------------------------------

BuildRotorCatalog() {
    return Map(
        "I", Map("wiring", "EKMFLGDQVZNTOWYHXUSPAIBRCJ", "notch", "Q"),
        "II", Map("wiring", "AJDKSIRUXBLHWTMCQGZNPYFVOE", "notch", "E"),
        "III", Map("wiring", "BDFHJLCPRTXVZNYEIWGAKMUSQO", "notch", "V"),
        "IV", Map("wiring", "ESOVPZJAYQUIRHXLNFTGKDCMWB", "notch", "J"),
        "V", Map("wiring", "VZBRGITYUPSDNHLXAWMJQOFECK", "notch", "Z"),
        "VI", Map("wiring", "JPGVOUMFYQBENHZRDKASXLICTW", "notch", "ZM"),
        "VII", Map("wiring", "NZJHGRCXMYSWBOUFAIVLPEKQDT", "notch", "ZM"),
        "VIII", Map("wiring", "FKQHTLXOCBJSPDZRAMEWNIUYGV", "notch", "ZM"),
        "Beta", Map("wiring", "LEYJVCNIXWPBQMDRTAKZGFUHOS", "notch", ""),
        "Gamma", Map("wiring", "FSOKANUERHMBTIYCWLQPZXVGJD", "notch", "")
    )
}

BuildReflectorCatalog() {
    return Map(
        "B", "YRUHQSLDPXNGOKMIEBFZCWVJAT",
        "C", "FVPJIAOYEDRZXWGCTKUQSBNMHL",
        "B Thin", "ENKQAUYWJICOPBLMDXZVFTHRGS",
        "C Thin", "RDOBJNTKVEHMLFCWZAXGYIPSUQ"
    )
}

BuildPlugboard(pairsText) {
    global ALPHABET
    plug := Map()
    used := Map()
    Loop 26 {
        letter := SubStr(ALPHABET, A_Index, 1)
        plug[letter] := letter
    }
    clean := RegExReplace(StrUpper(pairsText), "[^A-Z]", " ")
    pairs := StrSplit(clean, " ")
    for pair in pairs {
        if StrLen(pair) != 2
            continue
        a := SubStr(pair, 1, 1)
        b := SubStr(pair, 2, 1)
        if !InStr(ALPHABET, a) || !InStr(ALPHABET, b)
            continue
        if a = b
            continue
        if used.Has(a) || used.Has(b)
            continue
        plug[a] := b
        plug[b] := a
        used[a] := true
        used[b] := true
    }
    return plug
}

EnigmaEncryptLetter(letter) {
    global modeName, plugboard, enigmaThin, enigmaLeft, enigmaMiddle, enigmaRight, enigmaReflector, rotorPositions, enigmaRings, REFLECTOR_CATALOG

    StepEnigmaRotors()
    upper := StrUpper(letter)
    if !plugboard.Has(upper)
        return letter

    upper := plugboard[upper]

    if modeName = "Enigma M4" {
        upper := RotorForward(upper, enigmaRight, rotorPositions[4], SubStr(enigmaRings, 4, 1))
        upper := RotorForward(upper, enigmaMiddle, rotorPositions[3], SubStr(enigmaRings, 3, 1))
        upper := RotorForward(upper, enigmaLeft, rotorPositions[2], SubStr(enigmaRings, 2, 1))
        upper := RotorForward(upper, enigmaThin, rotorPositions[1], SubStr(enigmaRings, 1, 1))
        upper := SubStr(REFLECTOR_CATALOG[enigmaReflector], LetterIndex(upper) + 1, 1)
        upper := RotorBackward(upper, enigmaThin, rotorPositions[1], SubStr(enigmaRings, 1, 1))
        upper := RotorBackward(upper, enigmaLeft, rotorPositions[2], SubStr(enigmaRings, 2, 1))
        upper := RotorBackward(upper, enigmaMiddle, rotorPositions[3], SubStr(enigmaRings, 3, 1))
        upper := RotorBackward(upper, enigmaRight, rotorPositions[4], SubStr(enigmaRings, 4, 1))
    } else {
        upper := RotorForward(upper, enigmaRight, rotorPositions[3], SubStr(enigmaRings, 3, 1))
        upper := RotorForward(upper, enigmaMiddle, rotorPositions[2], SubStr(enigmaRings, 2, 1))
        upper := RotorForward(upper, enigmaLeft, rotorPositions[1], SubStr(enigmaRings, 1, 1))
        upper := SubStr(REFLECTOR_CATALOG[enigmaReflector], LetterIndex(upper) + 1, 1)
        upper := RotorBackward(upper, enigmaLeft, rotorPositions[1], SubStr(enigmaRings, 1, 1))
        upper := RotorBackward(upper, enigmaMiddle, rotorPositions[2], SubStr(enigmaRings, 2, 1))
        upper := RotorBackward(upper, enigmaRight, rotorPositions[3], SubStr(enigmaRings, 3, 1))
    }

    upper := plugboard[upper]
    return IsUpperLetter(letter) ? upper : StrLower(upper)
}

StepEnigmaRotors() {
    global modeName, rotorPositions, enigmaLeft, enigmaMiddle, enigmaRight

    if modeName = "Enigma M4" {
        leftIdx := 2, middleIdx := 3, rightIdx := 4
    } else {
        leftIdx := 1, middleIdx := 2, rightIdx := 3
    }

    leftStep := false
    middleStep := false
    rightStep := true

    if RotorAtNotch(enigmaMiddle, rotorPositions[middleIdx]) {
        leftStep := true
        middleStep := true
    }
    if RotorAtNotch(enigmaRight, rotorPositions[rightIdx])
        middleStep := true

    if leftStep
        rotorPositions[leftIdx] := RotateLetter(rotorPositions[leftIdx])
    if middleStep
        rotorPositions[middleIdx] := RotateLetter(rotorPositions[middleIdx])
    if rightStep
        rotorPositions[rightIdx] := RotateLetter(rotorPositions[rightIdx])
}

RotorAtNotch(rotorName, position) {
    global ROTOR_CATALOG
    notches := ROTOR_CATALOG[rotorName]["notch"]
    return notches != "" && InStr(notches, position)
}

RotorForward(letter, rotorName, position, ring) {
    global ROTOR_CATALOG
    wiring := ROTOR_CATALOG[rotorName]["wiring"]
    shift := LetterIndex(position) - LetterIndex(ring)
    inputIndex := LetterIndex(letter)
    shiftedIndex := PositiveMod(inputIndex + shift, 26)
    wiredLetter := SubStr(wiring, shiftedIndex + 1, 1)
    outputIndex := PositiveMod(LetterIndex(wiredLetter) - shift, 26)
    return LetterFromIndex(outputIndex, true)
}

RotorBackward(letter, rotorName, position, ring) {
    global ROTOR_CATALOG, ALPHABET
    wiring := ROTOR_CATALOG[rotorName]["wiring"]
    shift := LetterIndex(position) - LetterIndex(ring)
    inputIndex := LetterIndex(letter)
    shiftedIndex := PositiveMod(inputIndex + shift, 26)
    shiftedLetter := SubStr(ALPHABET, shiftedIndex + 1, 1)
    wiredIndex := InStr(wiring, shiftedLetter) - 1
    outputIndex := PositiveMod(wiredIndex - shift, 26)
    return LetterFromIndex(outputIndex, true)
}

PositionsToString() {
    global rotorPositions
    out := ""
    for _, ch in rotorPositions
        out .= ch
    return out
}

RotateLetter(letter) {
    global ALPHABET
    index := InStr(ALPHABET, letter)
    return SubStr(ALPHABET, Mod(index, 26) + 1, 1)
}

; ------------------------------------------------------------
; Other ciphers
; ------------------------------------------------------------

ShiftLetter(letter, shift) {
    idx := LetterIndex(StrUpper(letter))
    return LetterFromIndex(PositiveMod(idx + shift, 26), IsUpperLetter(letter))
}

AtbashLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    return LetterFromIndex(25 - idx, IsUpperLetter(letter))
}

SubstituteFromAlphabet(letter, alphabet) {
    idx := LetterIndex(StrUpper(letter))
    mapped := SubStr(alphabet, idx + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

KeywordAlphabet(keyword) {
    global ALPHABET
    clean := CleanLetters(keyword)
    out := ""
    for _, ch in StrSplit(clean) {
        if !InStr(out, ch)
            out .= ch
    }
    for _, ch in StrSplit(ALPHABET) {
        if !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 26)
}

DvorakLetter(letter) {
    dvorak := "AXJEUIDCHTNMBRLPOYGKQFVSZW"
    idx := LetterIndex(StrUpper(letter))
    mapped := SubStr(dvorak, idx + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

LeetLetter(letter) {
    upper := StrUpper(letter)
    leet := Map(
        "A", "4", "B", "8", "C", "C", "D", "D", "E", "3", "F", "F", "G", "6",
        "H", "H", "I", "1", "J", "J", "K", "K", "L", "1", "M", "M", "N", "N",
        "O", "0", "P", "P", "Q", "Q", "R", "R", "S", "5", "T", "7", "U", "U",
        "V", "V", "W", "W", "X", "X", "Y", "Y", "Z", "2"
    )
    return leet.Has(upper) ? leet[upper] : letter
}

MorseLetter(letter) {
    upper := StrUpper(letter)
    morse := Map(
        "A", ".- ", "B", "-... ", "C", "-.-. ", "D", "-.. ", "E", ". ", "F", "..-. ",
        "G", "--. ", "H", ".... ", "I", ".. ", "J", ".--- ", "K", "-.- ", "L", ".-.. ",
        "M", "-- ", "N", "-. ", "O", "--- ", "P", ".--. ", "Q", "--.- ", "R", ".-. ",
        "S", "... ", "T", "- ", "U", "..- ", "V", "...- ", "W", ".-- ", "X", "-..- ",
        "Y", "-.-- ", "Z", "--.. "
    )
    return morse.Has(upper) ? morse[upper] : letter
}

Binary5Letter(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    out := ""
    mask := 16
    while mask >= 1 {
        out .= (idx & mask) ? "1" : "0"
        mask := Floor(mask / 2)
    }
    return out . " "
}

NatoLetter(letter) {
    upper := StrUpper(letter)
    nato := Map(
        "A", "Alpha ", "B", "Bravo ", "C", "Charlie ", "D", "Delta ", "E", "Echo ", "F", "Foxtrot ",
        "G", "Golf ", "H", "Hotel ", "I", "India ", "J", "Juliett ", "K", "Kilo ", "L", "Lima ",
        "M", "Mike ", "N", "November ", "O", "Oscar ", "P", "Papa ", "Q", "Quebec ", "R", "Romeo ",
        "S", "Sierra ", "T", "Tango ", "U", "Uniform ", "V", "Victor ", "W", "Whiskey ", "X", "X-ray ",
        "Y", "Yankee ", "Z", "Zulu "
    )
    return nato.Has(upper) ? nato[upper] : letter
}

AzertyLetter(letter) {
    u := StrUpper(letter)
    switch u {
        case "A": out := "Q"
        case "Q": out := "A"
        case "W": out := "Z"
        case "Z": out := "W"
        case "M": out := ","
        default: out := u
    }
    return IsUpperLetter(letter) ? out : StrLower(out)
}

KeyboardMirrorLetter(letter) {
    m := Map(
        "Q","P", "W","O", "E","I", "R","U", "T","Y", "Y","T", "U","R", "I","E", "O","W", "P","Q",
        "A","L", "S","K", "D","J", "F","H", "G","G", "H","F", "J","D", "K","S", "L","A",
        "Z","M", "X","N", "C","B", "V","V", "B","C", "N","X", "M","Z"
    )
    u := StrUpper(letter)
    out := m.Has(u) ? m[u] : u
    return IsUpperLetter(letter) ? out : StrLower(out)
}

BaconianLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    out := ""
    mask := 16
    while mask >= 1 {
        out .= (idx & mask) ? "B" : "A"
        mask := Floor(mask / 2)
    }
    return out . " "
}

A1Z26Letter(letter) {
    return (LetterIndex(StrUpper(letter)) + 1) . " "
}

PolybiusLetter(letter) {
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    square := "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    row := Floor(idx / 5) + 1
    col := Mod(idx, 5) + 1
    return row . col . " "
}

TapCodeLetter(letter) {
    u := StrUpper(letter)
    if u = "K"
        u := "C"
    square := "ABCDEFGHIJLMNOPQRSTUVWXYZ" ; tap code combines C/K
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    row := Floor(idx / 5) + 1
    col := Mod(idx, 5) + 1
    return RepeatText(".", row) . " " . RepeatText(".", col) . " / "
}

ADFGXLetter(letter) {
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    square := "PHQGIUMEAYLNOFDXKRCVSTZWB"
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    labels := "ADFGX"
    row := Floor(idx / 5) + 1
    col := Mod(idx, 5) + 1
    return SubStr(labels, row, 1) . SubStr(labels, col, 1) . " "
}

HexAsciiLetter(letter) {
    return Format("{:02X} ", Ord(IsUpperLetter(letter) ? StrUpper(letter) : StrLower(letter)))
}

AsciiDecimalLetter(letter) {
    return Ord(IsUpperLetter(letter) ? StrUpper(letter) : StrLower(letter)) . " "
}

OctalAsciiLetter(letter) {
    return Format("{:03o} ", Ord(IsUpperLetter(letter) ? StrUpper(letter) : StrLower(letter)))
}

FullwidthLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    ch := Chr(0xFF21 + idx)
    return IsUpperLetter(letter) ? ch : Chr(0xFF41 + idx)
}

UpsideDownLetter(letter) {
    m := Map(
        "A","∀", "B","𐐒", "C","Ɔ", "D","◖", "E","Ǝ", "F","Ⅎ", "G","⅁", "H","H", "I","I", "J","ſ", "K","ʞ", "L","˥", "M","W",
        "N","N", "O","O", "P","Ԁ", "Q","Q", "R","ᴚ", "S","S", "T","⊥", "U","∩", "V","Λ", "W","M", "X","X", "Y","⅄", "Z","Z"
    )
    u := StrUpper(letter)
    out := m.Has(u) ? m[u] : letter
    return out
}

GreekLookalikeLetter(letter) {
    m := Map(
        "A","Α", "B","Β", "C","Ϲ", "D","Δ", "E","Ε", "F","Ϝ", "G","Ɠ", "H","Η", "I","Ι", "J","Ј", "K","Κ", "L","Λ", "M","Μ",
        "N","Ν", "O","Ο", "P","Ρ", "Q","Ϙ", "R","Я", "S","Σ", "T","Τ", "U","Ս", "V","Ν", "W","Ω", "X","Χ", "Y","Υ", "Z","Ζ"
    )
    u := StrUpper(letter)
    out := m.Has(u) ? m[u] : letter
    return out
}

CyrillicLookalikeLetter(letter) {
    m := Map(
        "A","А", "B","В", "C","С", "D","ᗪ", "E","Е", "F","Ғ", "G","Ԍ", "H","Н", "I","І", "J","Ј", "K","К", "L","ᒪ", "M","М",
        "N","И", "O","О", "P","Р", "Q","Ⴓ", "R","Я", "S","Ѕ", "T","Т", "U","Ц", "V","Ѵ", "W","Ш", "X","Х", "Y","У", "Z","Ζ"
    )
    u := StrUpper(letter)
    out := m.Has(u) ? m[u] : letter
    return out
}


ADFGVXLetter(letter) {
    u := StrUpper(letter)
    square := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    labels := "ADFGVX"
    row := Floor(idx / 6) + 1
    col := Mod(idx, 6) + 1
    return SubStr(labels, row, 1) . SubStr(labels, col, 1) . " "
}

StraddlingCheckerboardLetter(letter) {
    return CheckerboardNumberLetter(letter, "37")
}

MonomeDinomeLetter(letter) {
    return CheckerboardNumberLetter(letter, "26")
}

CheckerboardNumberLetter(letter, rowDigits) {
    u := StrUpper(letter)
    order := "ETAOINSHRDLCUMWFGYPBVKJXQZ"
    pos := InStr(order, u)
    if pos <= 0
        return letter
    rd1 := SubStr(rowDigits, 1, 1)
    rd2 := SubStr(rowDigits, 2, 1)
    topDigits := []
    Loop 10 {
        d := A_Index - 1
        ds := d . ""
        if ds != rd1 && ds != rd2
            topDigits.Push(ds)
    }
    if pos <= 8
        return topDigits[pos] . " "
    pos2 := pos - 9
    row := Floor(pos2 / 10)
    col := Mod(pos2, 10)
    return (row = 0 ? rd1 : rd2) . col . " "
}

PolluxMorseLetter(letter) {
    morse := Trim(MorseLetter(letter))
    if morse = ""
        return letter
    dotDigits := ["1", "2", "5"]
    dashDigits := ["3", "4", "6"]
    sepDigits := ["7", "8", "9", "0"]
    out := ""
    for _, ch in StrSplit(morse) {
        if ch = "."
            out .= dotDigits[Random(1, dotDigits.Length)]
        else if ch = "-"
            out .= dashDigits[Random(1, dashDigits.Length)]
    }
    out .= sepDigits[Random(1, sepDigits.Length)]
    return out . " "
}

Base64PerLetter(letter) {
    b := Ord(letter)
    alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    i1 := (b >> 2) + 1
    i2 := ((b & 3) << 4) + 1
    return SubStr(alpha, i1, 1) . SubStr(alpha, i2, 1) . "== "
}

UrlPercentLetter(letter) {
    return "%" . Format("{:02X}", Ord(letter)) . " "
}

HtmlEntityLetter(letter) {
    return "&#" . Ord(letter) . "; "
}

UnicodeCodePointLetter(letter) {
    return "U+" . Format("{:04X}", Ord(letter)) . " "
}

AsciiBinary8Letter(letter) {
    return ByteToBinary8(Ord(letter)) . " "
}

XorHexLetter(letter) {
    global keyText, streamIndex
    kb := XorKeyByte(streamIndex)
    streamIndex += 1
    return Format("{:02X}", Ord(letter) ^ kb) . " "
}

XorBinaryLetter(letter) {
    global keyText, streamIndex
    kb := XorKeyByte(streamIndex)
    streamIndex += 1
    return ByteToBinary8(Ord(letter) ^ kb) . " "
}

XorKeyByte(index) {
    global keyText
    key := keyText
    if key = ""
        key := "KEY"
    pos := PositiveMod(index, StrLen(key)) + 1
    return Ord(SubStr(key, pos, 1))
}

ByteToBinary8(value) {
    out := ""
    mask := 128
    while mask >= 1 {
        out .= (value & mask) ? "1" : "0"
        mask := Floor(mask / 2)
    }
    return out
}

BrailleLetter(letter) {
    patterns := Map(
        "A",0x2801, "B",0x2803, "C",0x2809, "D",0x2819, "E",0x2811, "F",0x280B, "G",0x281B,
        "H",0x2813, "I",0x280A, "J",0x281A, "K",0x2805, "L",0x2807, "M",0x280D, "N",0x281D,
        "O",0x2815, "P",0x280F, "Q",0x281F, "R",0x2817, "S",0x280E, "T",0x281E, "U",0x2825,
        "V",0x2827, "W",0x283A, "X",0x282D, "Y",0x283D, "Z",0x2835
    )
    u := StrUpper(letter)
    return patterns.Has(u) ? Chr(patterns[u]) : letter
}

PigpenLetter(letter) {
    symbols := Map(
        "A","⌜", "B","⊓", "C","⌝", "D","⊏", "E","□", "F","⊐", "G","⌞", "H","⊔", "I","⌟",
        "J","⌜·", "K","⊓·", "L","⌝·", "M","⊏·", "N","□·", "O","⊐·", "P","⌞·", "Q","⊔·", "R","⌟·",
        "S","△", "T","▷", "U","▽", "V","◁", "W","△·", "X","▷·", "Y","▽·", "Z","◁·"
    )
    u := StrUpper(letter)
    return symbols.Has(u) ? symbols[u] . " " : letter
}

EmojiLetter(letter) {
    emojis := ["😀","😃","😄","😁","😆","😅","😂","🙂","🙃","😉","😊","😎","🤓","🤠","😺","😸","😹","😻","🐱","🐶","🐼","🦊","🐸","🐵","🐙","⭐"]
    idx := LetterIndex(StrUpper(letter)) + 1
    return emojis[idx] . " "
}

LetterIndexHexLetter(letter) {
    return Format("{:02X}", LetterIndex(StrUpper(letter)) + 1) . " "
}

RomanNumeralLetter(letter) {
    return ToRoman(LetterIndex(StrUpper(letter)) + 1) . " "
}

PrimeNumberLetter(letter) {
    primes := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101]
    return primes[LetterIndex(StrUpper(letter)) + 1] . " "
}

SquaredA1Z26Letter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return (n * n) . " "
}

ToRoman(n) {
    vals := [10,9,5,4,1]
    nums := ["X","IX","V","IV","I"]
    out := ""
    for i, v in vals {
        while n >= v {
            out .= nums[i]
            n -= v
        }
    }
    return out
}

CondiLetter(letter) {
    global keyText, condiShift
    alpha := KeywordAlphabet(keyText)
    u := StrUpper(letter)
    pidx := InStr(alpha, u) - 1
    if pidx < 0
        return letter
    cidx := PositiveMod(pidx + condiShift, 26)
    mapped := SubStr(alpha, cidx + 1, 1)
    condiShift := PositiveMod(pidx + 1, 26)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

ChaocipherLetter(letter) {
    global chaosLeft, chaosRight
    u := StrUpper(letter)
    idx := InStr(chaosRight, u)
    if idx <= 0
        return letter
    cipher := SubStr(chaosLeft, idx, 1)
    StepChaocipher(cipher, u)
    return IsUpperLetter(letter) ? cipher : StrLower(cipher)
}

StepChaocipher(cipher, plain) {
    global chaosLeft, chaosRight
    cidx := InStr(chaosLeft, cipher)
    pidx := InStr(chaosRight, plain)
    chaosLeft := SubStr(chaosLeft, cidx) . SubStr(chaosLeft, 1, cidx - 1)
    chaosRight := SubStr(chaosRight, pidx) . SubStr(chaosRight, 1, pidx - 1)
    chaosLeft := SubStr(chaosLeft, 1, 1) . SubStr(chaosLeft, 3, 12) . SubStr(chaosLeft, 2, 1) . SubStr(chaosLeft, 15)
    chaosRight := SubStr(chaosRight, 1, 2) . SubStr(chaosRight, 4, 11) . SubStr(chaosRight, 3, 1) . SubStr(chaosRight, 15)
}

PlayfairLetter(letter) {
    global pairBuffer
    u := StrUpper(letter)
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    return PlayfairEncryptPair(a, b, IsUpperLetter(letter))
}

FlushPendingByMode() {
    global modeName, pairBuffer
    if pairBuffer = ""
        return ""
    block := pairBuffer
    pairBuffer := ""
    switch modeName {
        case "Playfair pairs":
            return PlayfairEncryptPair(block, "X", true)
        case "Hill 2x2 pairs":
            return Hill2x2EncryptPair(block, "X", true)
        case "Bifid pairs":
            return BifidEncryptPair(block, "X", true)
        case "Two-square pairs":
            return TwoSquareEncryptPair(block, "X", true)
        case "Four-square pairs":
            return FourSquareEncryptPair(block, "X", true)
        case "Slidefair pairs":
            return SlidefairEncryptPair(block, "X", true)
        case "Rail fence block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "Rail") . " "
        case "Scytale transposition":
            return EncryptNamedBlock(PadRight(block, 8, "X"), "Scytale") . " "
        case "Columnar transposition block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "Columnar") . " "
        case "Double columnar block":
            return EncryptNamedBlock(PadRight(block, 12, "X"), "DoubleColumnar") . " "
        case "Route cipher block":
            return EncryptNamedBlock(PadRight(block, RouteBlockSize(), "X"), "Route") . " "
        case "Myszkowski transposition block":
            return EncryptNamedBlock(PadRight(block, 12, "X"), "Myszkowski") . " "
        case "Bifid full period":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "BifidFull") . " "
        case "Trifid full period":
            return EncryptNamedBlock(PadRight(block, 9, "X"), "TrifidFull") . " "
        case "Seriated Playfair pairs":
            return PlayfairEncryptPair(block, "X", true)
        case "Playfair 6x6 pairs":
            return Playfair6x6EncryptPair(block, "X", true)
        case "Two-square vertical pairs":
            return TwoSquareVerticalEncryptPair(block, "X", true)
        case "Tri-square triples":
            return TriSquareEncryptPair(block, "X", true)
        case "Two-square 6x6 pairs":
            return TwoSquare6x6EncryptPair(block, "X", true)
        case "Four-square 6x6 pairs":
            return FourSquare6x6EncryptPair(block, "X", true)
        case "Bifid 6x6 pairs":
            return Bifid6x6EncryptPair(block, "X", true)
        case "Hill 3x3 block":
            return EncryptNamedBlock(PadRight(block, 3, "X"), "Hill3") . " "
        case "Nicodemus block":
            return EncryptNamedBlock(PadRight(block, 12, "X"), "Nicodemus") . " "
        case "Cadenus block":
            return EncryptNamedBlock(PadRight(block, 25, "X"), "Cadenus") . " "
        case "AMSCO block":
            return EncryptNamedBlock(PadRight(block, 12, "X"), "AMSCO") . " "
        case "Swagman block":
            return EncryptNamedBlock(PadRight(block, 8, "X"), "Swagman") . " "
        case "Bazeries block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "Bazeries") . " "
        case "Disrupted transposition block":
            return EncryptNamedBlock(PadRight(block, 12, "X"), "Disrupted") . " "
        case "Incomplete columnar block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "IncompleteColumnar") . " "
        case "Complete columnar block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "CompleteColumnar") . " "
        case "Alternating columnar block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "AlternatingColumnar") . " "
        case "Boustrophedon route block":
            return EncryptNamedBlock(PadRight(block, RouteBlockSize(), "X"), "Boustrophedon") . " "
        case "Spiral inward route block":
            return EncryptNamedBlock(PadRight(block, RouteBlockSize(), "X"), "SpiralIn") . " "
        case "Spiral outward route block":
            return EncryptNamedBlock(PadRight(block, RouteBlockSize(), "X"), "SpiralOut") . " "
        case "Reading order route block":
            return EncryptNamedBlock(PadRight(block, RouteBlockSize(), "X"), "ReadingRoute") . " "
        case "Rotating square route block":
            return EncryptNamedBlock(PadRight(block, RouteBlockSize(), "X"), "RotatingSquare") . " "
        case "Grille mask block":
            return EncryptNamedBlock(PadRight(block, 25, "X"), "GrilleMask") . " "
        case "Fleissner grille block":
            return EncryptNamedBlock(PadRight(block, 16, "X"), "Fleissner") . " "
        case "Redefence rail offset block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "Redefence") . " "
        case "Polybius columnar block":
            return EncryptNamedBlock(PadRight(block, 10, "X"), "PolybiusColumnar") . " "
        case "Playfair Q omitted pairs":
            return PlayfairQOmittedEncryptPair(block, "X", true)
        case "Double Playfair pairs":
            return DoublePlayfairEncryptPair(block, "X", true)
        case "Twin Bifid pairs":
            return TwinBifidEncryptPair(block, "X", true)
        case "Caesar box mini block":
            return TransformMiniBlock(PadRight(block, 9, "X"), "CaesarBox") . " "
        case "Skip permutation block":
            return TransformMiniBlock(PadRight(block, 8, "X"), "SkipPermutation") . " "
        case "Vertical transposition block":
            return TransformMiniBlock(PadRight(block, 8, "X"), "VerticalTransposition") . " "
        case "Rail fence spaces block":
            return TransformMiniBlock(PadRight(block, 8, "X"), "RailFenceSpaces") . " "
    }
    ; Later historical aliases sometimes route to the same buffered Bifid/Trifid engines
    ; without having their exact mode name listed above. Flush them safely at boundaries.
    if InStr(modeName, "Trifid")
        return EncryptNamedBlock(PadRight(block, 9, "X"), "TrifidFull") . " "
    if InStr(modeName, "Bifid")
        return EncryptNamedBlock(PadRight(block, 10, "X"), "BifidFull") . " "
    if InStr(modeName, "Hill 3x3")
        return EncryptNamedBlock(PadRight(block, 3, "X"), "Hill3") . " "
    return ""
}

PlayfairEncryptPair(a, b, uppercase := true) {
    global keyText
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    if a = b
        b := "X"
    square := PlayfairSquare(keyText)
    ia := InStr(square, a) - 1
    ib := InStr(square, b) - 1
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    if ra = rb {
        c1 := SubStr(square, ra * 5 + Mod(ca + 1, 5) + 1, 1)
        c2 := SubStr(square, rb * 5 + Mod(cb + 1, 5) + 1, 1)
    } else if ca = cb {
        c1 := SubStr(square, Mod(ra + 1, 5) * 5 + ca + 1, 1)
        c2 := SubStr(square, Mod(rb + 1, 5) * 5 + cb + 1, 1)
    } else {
        c1 := SubStr(square, ra * 5 + cb + 1, 1)
        c2 := SubStr(square, rb * 5 + ca + 1, 1)
    }
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

PlayfairSquare(key) {
    clean := StrReplace(CleanLetters(key), "J", "I")
    base := "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    out := ""
    for _, ch in StrSplit(clean . base) {
        if !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 25)
}


Hill2x2Letter(letter) {
    global pairBuffer
    u := StrUpper(letter)
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    return Hill2x2EncryptPair(a, b, IsUpperLetter(letter))
}

Hill2x2EncryptPair(a, b, uppercase := true) {
    x := LetterIndex(a)
    y := LetterIndex(b)
    c1 := PositiveMod(3 * x + 3 * y, 26)
    c2 := PositiveMod(2 * x + 5 * y, 26)
    out := LetterFromIndex(c1, true) . LetterFromIndex(c2, true)
    return uppercase ? out : StrLower(out)
}

BifidLetter(letter) {
    global pairBuffer
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    return BifidEncryptPair(a, b, IsUpperLetter(letter))
}

BifidEncryptPair(a, b, uppercase := true) {
    global keyText
    square := PlayfairSquare(keyText)
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    ia := InStr(square, a) - 1
    ib := InStr(square, b) - 1
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    c1 := SubStr(square, ra * 5 + rb + 1, 1)
    c2 := SubStr(square, ca * 5 + cb + 1, 1)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

TwoSquareLetter(letter) {
    global pairBuffer
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    return TwoSquareEncryptPair(a, b, IsUpperLetter(letter))
}

TwoSquareEncryptPair(a, b, uppercase := true) {
    global keyText
    leftSquare := PlayfairSquare(keyText)
    rightSquare := PlayfairSquare("SQUARE" . keyText)
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    ia := InStr(leftSquare, a) - 1
    ib := InStr(rightSquare, b) - 1
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    if ra = rb {
        c1 := a
        c2 := b
    } else {
        c1 := SubStr(leftSquare, ra * 5 + cb + 1, 1)
        c2 := SubStr(rightSquare, rb * 5 + ca + 1, 1)
    }
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

FourSquareLetter(letter) {
    global pairBuffer
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    return FourSquareEncryptPair(a, b, IsUpperLetter(letter))
}

FourSquareEncryptPair(a, b, uppercase := true) {
    global keyText
    plainSquare := "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    topRight := PlayfairSquare(keyText)
    bottomLeft := PlayfairSquare("FOUR" . keyText)
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    ia := InStr(plainSquare, a) - 1
    ib := InStr(plainSquare, b) - 1
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    c1 := SubStr(topRight, ra * 5 + cb + 1, 1)
    c2 := SubStr(bottomLeft, rb * 5 + ca + 1, 1)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

NihilistLetter(letter) {
    global keyText, streamIndex
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    p := PolybiusNumberForLetter(u)
    kshift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    kletter := LetterFromIndex(kshift, true)
    if kletter = "J"
        kletter := "I"
    k := PolybiusNumberForLetter(kletter)
    return (p + k) . " "
}

PolybiusNumberForLetter(u) {
    if u = "J"
        u := "I"
    square := "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    idx := InStr(square, u) - 1
    row := Floor(idx / 5) + 1
    col := Mod(idx, 5) + 1
    return (row * 10) + col
}

TrifidCoordinateLetter(letter) {
    cube := "ABCDEFGHIJKLMNOPQRSTUVWXYZ."
    u := StrUpper(letter)
    idx := InStr(cube, u) - 1
    if idx < 0
        return letter
    layer := Floor(idx / 9) + 1
    rem := Mod(idx, 9)
    row := Floor(rem / 3) + 1
    col := Mod(rem, 3) + 1
    return layer . row . col . " "
}

CheckerboardCoordinateLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    row := Floor(idx / 6) + 1
    col := Mod(idx, 6) + 1
    return row . "," . col . " "
}

BaudotLetter(letter) {
    u := StrUpper(letter)
    codes := Map(
        "A","00011", "B","11001", "C","01110", "D","01001", "E","00001", "F","01101",
        "G","11010", "H","10100", "I","00110", "J","01011", "K","01111", "L","10010",
        "M","11100", "N","01100", "O","11000", "P","10110", "Q","10111", "R","01010",
        "S","00101", "T","10000", "U","00111", "V","11110", "W","10011", "X","11101",
        "Y","10101", "Z","10001"
    )
    return codes.Has(u) ? codes[u] . " " : letter
}

GrayCode5Letter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    g := n ^ (n >> 1)
    return ToBinaryWidth(g, 5) . " "
}

BcdA1Z26Letter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    tens := Floor(n / 10)
    ones := Mod(n, 10)
    return ToBinaryWidth(tens, 4) . " " . ToBinaryWidth(ones, 4) . " "
}

FibonacciNumberLetter(letter) {
    fib := [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765,10946,17711,28657,46368,75025,121393]
    return fib[LetterIndex(StrUpper(letter)) + 1] . " "
}

TriangularNumberLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return Floor(n * (n + 1) / 2) . " "
}

CubedA1Z26Letter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return (n * n * n) . " "
}

FactorialIndexLetter(letter) {
    facts := ["1","2","6","24","120","720","5040","40320","362880","3628800","39916800","479001600","6227020800","87178291200","1307674368000","20922789888000","355687428096000","6402373705728000","121645100408832000","2432902008176640000","51090942171709440000","1124000727777607680000","25852016738884976640000","620448401733239439360000","15511210043330985984000000","403291461126605635584000000"]
    return facts[LetterIndex(StrUpper(letter)) + 1] . " "
}

Modulo9IndexLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    r := Mod(n, 9)
    if r = 0
        r := 9
    return r . " "
}

ReverseAlphabetIndexLetter(letter) {
    return (26 - LetterIndex(StrUpper(letter))) . " "
}

KeyboardCaesarLetter(letter) {
    global shiftValue
    keys := "QWERTYUIOPASDFGHJKLZXCVBNM"
    u := StrUpper(letter)
    idx := InStr(keys, u) - 1
    if idx < 0
        return letter
    mapped := SubStr(keys, PositiveMod(idx + shiftValue, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

VowelCaesarLetter(letter) {
    global shiftValue
    vowels := "AEIOU"
    u := StrUpper(letter)
    idx := InStr(vowels, u) - 1
    if idx < 0
        return letter
    mapped := SubStr(vowels, PositiveMod(idx + shiftValue, 5) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

ConsonantCaesarLetter(letter) {
    global shiftValue
    cons := "BCDFGHJKLMNPQRSTVWXYZ"
    u := StrUpper(letter)
    idx := InStr(cons, u) - 1
    if idx < 0
        return letter
    mapped := SubStr(cons, PositiveMod(idx + shiftValue, 21) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

AlternatingCaesarLetter(letter) {
    global shiftValue, streamIndex
    shift := (Mod(streamIndex, 2) = 0) ? shiftValue : -shiftValue
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

FutharkLetter(letter) {
    runes := ["ᚠ","ᚢ","ᚦ","ᚨ","ᚱ","ᚲ","ᚷ","ᚹ","ᚺ","ᚾ","ᛁ","ᛃ","ᛇ","ᛈ","ᛉ","ᛊ","ᛏ","ᛒ","ᛖ","ᛗ","ᛚ","ᛜ","ᛞ","ᛟ","ᚡ","ᛦ"]
    return runes[LetterIndex(StrUpper(letter)) + 1] . " "
}

OghamLetter(letter) {
    ogham := ["ᚐ","ᚁ","ᚉ","ᚇ","ᚓ","ᚃ","ᚌ","ᚆ","ᚔ","ᚊ","ᚕ","ᚂ","ᚋ","ᚅ","ᚑ","ᚚ","ᚊ","ᚏ","ᚄ","ᚈ","ᚒ","ᚃ","ᚃ","ᚎ","ᚔ","ᚎ"]
    return ogham[LetterIndex(StrUpper(letter)) + 1] . " "
}

SemaphoreTextLetter(letter) {
    sem := Map(
        "A","down-left + down", "B","down-left + down-right", "C","down-left + right", "D","down-left + up-right", "E","down-left + up", "F","down-left + up-left", "G","down + down-right",
        "H","down + right", "I","down + up-right", "J","right + up", "K","down + up", "L","down + up-left", "M","down-right + right", "N","down-right + up-right",
        "O","down-right + up", "P","down-right + up-left", "Q","right + up-right", "R","right + up", "S","right + up-left", "T","up-right + up", "U","up-right + up-left",
        "V","up + up-left", "W","down + left", "X","down-right + left", "Y","right + left", "Z","up-right + left"
    )
    u := StrUpper(letter)
    return sem.Has(u) ? "[" . sem[u] . "] " : letter
}

MasonicPigpenVariantLetter(letter) {
    symbols := Map(
        "A","□1", "B","□2", "C","□3", "D","□4", "E","□5", "F","□6", "G","□7", "H","□8", "I","□9",
        "J","□1·", "K","□2·", "L","□3·", "M","□4·", "N","□5·", "O","□6·", "P","□7·", "Q","□8·", "R","□9·",
        "S","◇1", "T","◇2", "U","◇3", "V","◇4", "W","◇1·", "X","◇2·", "Y","◇3·", "Z","◇4·"
    )
    u := StrUpper(letter)
    return symbols.Has(u) ? symbols[u] . " " : letter
}



QuagmireILetter(letter) {
    return QuagmireLetter(letter, 1)
}

IsQuagmireMode(mode) {
    return mode = "Quagmire I" || mode = "Quagmire II" || mode = "Quagmire III" || mode = "Quagmire IV"
}

QuagmireLetter(letter, variant) {
    global quagPlainKey, quagCipherKey, quagIndicatorKey, quagIndicatorPos, streamIndex, ALPHABET

    plainKey := CleanLetters(quagPlainKey)
    if plainKey = ""
        plainKey := "CIPHER"

    cipherKey := CleanLetters(quagCipherKey)
    if cipherKey = ""
        cipherKey := "MONARCHY"

    indicator := CleanLetters(quagIndicatorKey)
    if indicator = ""
        indicator := "SECRET"

    indicatorPos := SubStr(CleanLetters(quagIndicatorPos), 1, 1)
    if indicatorPos = ""
        indicatorPos := "A"

    ; Quagmire variants as periodic mixed-alphabet substitutions:
    ; I   = keyed plaintext alphabet + normal ciphertext alphabet + indicator key
    ; II  = normal plaintext alphabet + keyed ciphertext alphabet + indicator key
    ; III = keyed plaintext alphabet + same keyed ciphertext alphabet + indicator key
    ; IV  = keyed plaintext alphabet + separate keyed ciphertext alphabet + indicator key
    if variant = 1 {
        plainAlphabet := KeywordAlphabet(plainKey)
        cipherAlphabet := ALPHABET
    } else if variant = 2 {
        plainAlphabet := ALPHABET
        cipherAlphabet := KeywordAlphabet(cipherKey)
    } else if variant = 3 {
        plainAlphabet := KeywordAlphabet(plainKey)
        cipherAlphabet := KeywordAlphabet(plainKey)
    } else {
        plainAlphabet := KeywordAlphabet(plainKey)
        cipherAlphabet := KeywordAlphabet(cipherKey)
    }

    indChar := SubStr(indicator, Mod(streamIndex, StrLen(indicator)) + 1, 1)
    posCipherIndicator := InStr(cipherAlphabet, indChar)
    posPlainIndicator := InStr(plainAlphabet, indicatorPos)
    if posCipherIndicator <= 0
        posCipherIndicator := 1
    if posPlainIndicator <= 0
        posPlainIndicator := 1

    shift := (posCipherIndicator - posPlainIndicator)
    rowAlphabet := ShiftedAlphabet(cipherAlphabet, shift)
    streamIndex += 1
    return SubstituteBetweenAlphabets(letter, plainAlphabet, rowAlphabet)
}

SubstituteBetweenAlphabets(letter, sourceAlphabet, targetAlphabet) {
    u := StrUpper(letter)
    pos := InStr(sourceAlphabet, u)
    if pos <= 0
        return letter
    mapped := SubStr(targetAlphabet, pos, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

ShiftedAlphabet(alphabet, shift) {
    shift := PositiveMod(shift, StrLen(alphabet))
    return SubStr(alphabet, shift + 1) . SubStr(alphabet, 1, shift)
}

ReverseString(text) {
    out := ""
    for _, ch in StrSplit(text)
        out := ch . out
    return out
}

AlbertiDiskLetter(letter) {
    global keyText, streamIndex, ALPHABET
    disk := KeywordAlphabet(keyText)
    ; Rotating cipher disk; the disk advances one position per typed letter.
    target := ShiftedAlphabet(disk, streamIndex)
    streamIndex += 1
    return SubstituteBetweenAlphabets(letter, ALPHABET, target)
}

BellasoLetter(letter) {
    global keyText, streamIndex
    ; Bellaso-style reciprocal/Vigenere-like shifting with a keyed stream.
    shift := KeyShiftAt(keyText, streamIndex) + Floor(streamIndex / Max(1, StrLen(CleanLetters(keyText))))
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

AutokeyBeaufortLetter(letter) {
    global keyText, streamIndex, autoKeyHistory
    if streamIndex < StrLen(CleanLetters(keyText))
        shift := KeyShiftAt(keyText, streamIndex)
    else
        shift := KeyShiftAt(autoKeyHistory = "" ? "A" : autoKeyHistory, streamIndex - StrLen(CleanLetters(keyText)))
    p := LetterIndex(StrUpper(letter))
    c := PositiveMod(shift - p, 26)
    autoKeyHistory .= StrUpper(letter)
    streamIndex += 1
    return LetterFromIndex(c, IsUpperLetter(letter))
}

ProgressivePortaLetter(letter) {
    global keyText, streamIndex
    kidx := Floor(KeyShiftAt(keyText, streamIndex) / 2) + streamIndex
    streamIndex += 1
    x := LetterIndex(StrUpper(letter))
    if x < 13
        y := PositiveMod(x + 13 - kidx, 13) + 13
    else
        y := PositiveMod(x - 13 + kidx, 13)
    return LetterFromIndex(y, IsUpperLetter(letter))
}

GronsfeldProgressiveLetter(letter) {
    global keyText, streamIndex
    digits := CleanDigits(keyText)
    if digits = ""
        digits := "31415"
    d := SubStr(digits, PositiveMod(streamIndex, StrLen(digits)) + 1, 1) + 0
    shift := d + streamIndex
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

KeyedAtbashLetter(letter) {
    global keyText
    alpha := KeywordAlphabet(keyText)
    u := StrUpper(letter)
    pos := InStr(alpha, u)
    if pos <= 0
        return letter
    mapped := SubStr(alpha, 27 - pos, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}


DianaLetter(letter) {
    global keyText, streamIndex
    ; Diana-style reciprocal alphabet with key subtraction: C = 25 - (P + K) mod 26.
    k := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    p := LetterIndex(StrUpper(letter))
    c := PositiveMod(25 - p - k, 26)
    return LetterFromIndex(c, IsUpperLetter(letter))
}

FibonacciCaesarShiftLetter(letter) {
    global streamIndex
    fib := [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765,10946,17711,28657,46368,75025,121393]
    shift := fib[PositiveMod(streamIndex, fib.Length) + 1]
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

PrimeCaesarShiftLetter(letter) {
    global streamIndex
    primes := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101]
    shift := primes[PositiveMod(streamIndex, primes.Length) + 1]
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

HomophonicNumberLetter(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    ; Three possible homophones per letter, randomized every letter.
    base := idx * 3 - 2
    return Format("{:02d}", base + Random(0, 2)) . " "
}

Base32PerLetter(letter) {
    b := Ord(letter)
    alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
    i1 := (b >> 3) + 1
    i2 := ((b & 7) << 2) + 1
    return SubStr(alpha, i1, 1) . SubStr(alpha, i2, 1) . "====== "
}

QuotedPrintableLetter(letter) {
    ; Force encoded form so the transformation is visible for normal A-Z letters.
    return "=" . Format("{:02X}", Ord(letter)) . " "
}

DecimalA0Z25Letter(letter) {
    return LetterIndex(StrUpper(letter)) . " "
}

ZeroPaddedA1Z26Letter(letter) {
    return Format("{:02d}", LetterIndex(StrUpper(letter)) + 1) . " "
}

OctalA1Z26Letter(letter) {
    return Format("{:02o}", LetterIndex(StrUpper(letter)) + 1) . " "
}

Binary6IndexLetter(letter) {
    return ToBinaryWidth(LetterIndex(StrUpper(letter)) + 1, 6) . " "
}

Coordinate0BasedLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    row := Floor(idx / 6)
    col := Mod(idx, 6)
    return row . "," . col . " "
}

MorseCompact01Letter(letter) {
    morse := Trim(MorseLetter(letter))
    if morse = ""
        return letter
    out := ""
    for _, ch in StrSplit(morse) {
        if ch = "."
            out .= "0"
        else if ch = "-"
            out .= "1"
    }
    return out . " "
}

PolybiusReversedLetter(letter) {
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    square := "ZYXWVUTSRQPONMLKIHGFEDCBA"
    square := StrReplace(square, "J", "")
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    row := Floor(idx / 5) + 1
    col := Mod(idx, 5) + 1
    return row . col . " "
}

MaritimeFlagLetter(letter) {
    ; Unicode regional indicators render as signal-flag-like letters in many fonts.
    return Chr(0x1F1E6 + LetterIndex(StrUpper(letter))) . " "
}

RegionalIndicatorLetter(letter) {
    return Chr(0x1F1E6 + LetterIndex(StrUpper(letter))) . " "
}

CircledLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    ch := Chr(0x24B6 + idx)
    return ch . " "
}

SquaredUnicodeLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    if idx < 26
        return Chr(0x1F130 + idx) . " "
    return letter
}

ParenthesizedLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    if idx = 0
        return "⒜ "
    if idx >= 1 && idx <= 25
        return Chr(0x249C + idx) . " "
    return letter
}

FrakturLetter(letter) {
    chars := ["𝔄","𝔅","ℭ","𝔇","𝔈","𝔉","𝔊","ℌ","ℑ","𝔍","𝔎","𝔏","𝔐","𝔑","𝔒","𝔓","𝔔","ℜ","𝔖","𝔗","𝔘","𝔙","𝔚","𝔛","𝔜","ℨ"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

ScriptLetter(letter) {
    chars := ["𝒜","ℬ","𝒞","𝒟","ℰ","ℱ","𝒢","ℋ","ℐ","𝒥","𝒦","ℒ","ℳ","𝒩","𝒪","𝒫","𝒬","ℛ","𝒮","𝒯","𝒰","𝒱","𝒲","𝒳","𝒴","𝒵"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

SmallCapsLetter(letter) {
    chars := StrSplit("ᴀ|ʙ|ᴄ|ᴅ|ᴇ|ꜰ|ɢ|ʜ|ɪ|ᴊ|ᴋ|ʟ|ᴍ|ɴ|ᴏ|ᴘ|ǫ|ʀ|ꜱ|ᴛ|ᴜ|ᴠ|ᴡ|x|ʏ|ᴢ", "|")
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

SuperscriptLetter(letter) {
    chars := StrSplit("ᴬ|ᴮ|ᶜ|ᴰ|ᴱ|ᶠ|ᴳ|ᴴ|ᴵ|ᴶ|ᴷ|ᴸ|ᴹ|ᴺ|ᴼ|ᴾ|Q|ᴿ|ˢ|ᵀ|ᵁ|ⱽ|ᵂ|ˣ|ʸ|ᶻ", "|")
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

SubscriptLetter(letter) {
    chars := StrSplit("ₐ|ᵦ|꜀|ᑯ|ₑ|բ|₉|ₕ|ᵢ|ⱼ|ₖ|ₗ|ₘ|ₙ|ₒ|ₚ|q|ᵣ|ₛ|ₜ|ᵤ|ᵥ|w|ₓ|ᵧ|₂", "|")
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

ZalgoLightLetter(letter) {
    marks := [Chr(0x0301), Chr(0x0302), Chr(0x0303), Chr(0x0304), Chr(0x0307), Chr(0x0308), Chr(0x0332)]
    return letter . marks[Random(1, marks.Length)]
}

MirrorTextAlphabetLetter(letter) {
    chars := StrSplit("A|ᗺ|Ɔ|ᗡ|Ǝ|ꟻ|Ꭾ|H|I|Ⴑ|ꓘ|⅃|M|И|O|ꟼ|Ϙ|Я|S|T|U|V|W|X|Y|Z", "|")
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

ToBinaryWidth(value, width) {
    out := ""
    mask := 1 << (width - 1)
    while mask >= 1 {
        out .= (value & mask) ? "1" : "0"
        mask := mask >> 1
    }
    return out
}

RepeatText(text, count) {
    out := ""
    Loop count
        out .= text
    return out
}


; ------------------------------------------------------------
; More ciphers v5
; ------------------------------------------------------------

KeyedPolybiusLetter(letter) {
    global keyText
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    square := PlayfairSquare(keyText)
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    return (Floor(idx / 5) + 1) . (Mod(idx, 5) + 1) . " "
}

KeyedADFGXLetter(letter) {
    global keyText
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    square := PlayfairSquare(keyText)
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    labels := "ADFGX"
    return SubStr(labels, Floor(idx / 5) + 1, 1) . SubStr(labels, Mod(idx, 5) + 1, 1) . " "
}

KeyedADFGVXLetter(letter) {
    global keyText
    u := StrUpper(letter)
    square := KeyedAlphaNum36(keyText)
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    labels := "ADFGVX"
    return SubStr(labels, Floor(idx / 6) + 1, 1) . SubStr(labels, Mod(idx, 6) + 1, 1) . " "
}

KeyedAlphaNum36(key) {
    base := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    clean := RegExReplace(StrUpper(key), "[^A-Z0-9]", "")
    out := ""
    for _, ch in StrSplit(clean) {
        if InStr(base, ch) && !InStr(out, ch)
            out .= ch
    }
    for _, ch in StrSplit(base) {
        if !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 36)
}

MorbitMorseLetter(letter) {
    global keyText
    seq := StrReplace(Trim(MorseLetter(letter)), " ", "") . "x"
    if Mod(StrLen(seq), 2) = 1
        seq .= "x"
    triples := ["..", ".-", ".x", "-.", "--", "-x", "x.", "x-", "xx"]
    digits := MorbitDigitOrder(keyText)
    out := ""
    Loop StrLen(seq) // 2 {
        pair := SubStr(seq, (A_Index - 1) * 2 + 1, 2)
        idx := IndexOf(triples, pair)
        out .= SubStr(digits, idx, 1)
    }
    return out . " "
}

MorbitDigitOrder(key) {
    clean := CleanDigits(key)
    out := ""
    for _, ch in StrSplit(clean) {
        if ch != "0" && !InStr(out, ch)
            out .= ch
    }
    Loop 9 {
        d := A_Index . ""
        if !InStr(out, d)
            out .= d
    }
    return SubStr(out, 1, 9)
}

FractionatedMorseLetter(letter) {
    global keyText
    seq := StrReplace(Trim(MorseLetter(letter)), " ", "") . "x"
    while Mod(StrLen(seq), 3) != 0
        seq .= "x"
    codes := ["...", "..-", "..x", ".-.", ".--", ".-x", ".x.", ".x-", ".xx", "-..", "-.-", "-.x", "--.", "---", "--x", "-x.", "-x-", "-xx", "x..", "x.-", "x.x", "x-.", "x--", "x-x", "xx.", "xx-"]
    alpha := KeywordAlphabet(keyText)
    out := ""
    Loop StrLen(seq) // 3 {
        tri := SubStr(seq, (A_Index - 1) * 3 + 1, 3)
        idx := IndexOf(codes, tri)
        if idx >= 1 && idx <= 26
            out .= SubStr(alpha, idx, 1)
    }
    return out . " "
}

MorseReverseLetter(letter) {
    m := Trim(MorseLetter(letter))
    out := ""
    for _, ch in StrSplit(m) {
        if ch = "."
            out .= "-"
        else if ch = "-"
            out .= "."
    }
    return out . " "
}

MorseEmojiLetter(letter) {
    m := Trim(MorseLetter(letter))
    out := ""
    for _, ch in StrSplit(m) {
        if ch = "."
            out .= "·"
        else if ch = "-"
            out .= "━"
    }
    return out . " "
}

MorseTapDigitsLetter(letter) {
    m := Trim(MorseLetter(letter))
    out := ""
    for _, ch in StrSplit(m) {
        if ch = "."
            out .= "1"
        else if ch = "-"
            out .= "2"
    }
    return out . " "
}

Baconian24Letter(letter) {
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    if u = "V"
        u := "U"
    alpha := "ABCDEFGHIKLMNOPQRSTUWXYZ"
    idx := InStr(alpha, u) - 1
    if idx < 0
        return letter
    out := ""
    mask := 16
    while mask >= 1 {
        out .= (idx & mask) ? "B" : "A"
        mask := Floor(mask / 2)
    }
    return out . " "
}

KamasutraLetter(letter) {
    global keyText
    alpha := KeywordAlphabet(keyText)
    trans := Map()
    Loop 13 {
        a := SubStr(alpha, A_Index, 1)
        b := SubStr(alpha, A_Index + 13, 1)
        trans[a] := b
        trans[b] := a
    }
    u := StrUpper(letter)
    out := trans.Has(u) ? trans[u] : u
    return IsUpperLetter(letter) ? out : StrLower(out)
}

PhillipsLetter(letter) {
    global keyText, streamIndex
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    square := PhillipsSquareForGroup(keyText, Floor(streamIndex / 5))
    streamIndex += 1
    idx := InStr(square, u) - 1
    if idx < 0
        return letter
    r := Floor(idx / 5), c := Mod(idx, 5)
    mapped := SubStr(square, Mod(r + 1, 5) * 5 + c + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

PhillipsSquareForGroup(key, group) {
    square := PlayfairSquare(key)
    shift := Mod(group, 5)
    rows := []
    Loop 5
        rows.Push(SubStr(square, (A_Index - 1) * 5 + 1, 5))
    out := ""
    Loop 5 {
        idx := Mod(A_Index - 1 + shift, 5) + 1
        out .= rows[idx]
    }
    return out
}

SlidefairLetter(letter) {
    global pairBuffer
    u := StrUpper(letter)
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    return SlidefairEncryptPair(a, b, IsUpperLetter(letter))
}

SlidefairEncryptPair(a, b, uppercase := true) {
    global keyText, streamIndex
    k := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    ai := LetterIndex(a)
    bi := LetterIndex(b)
    c1 := LetterFromIndex(ai + k, true)
    c2 := LetterFromIndex(bi + ai + k, true)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

ColemakLetter(letter) {
    colemak := "QWFPGJLUYARSTDHNEIOZXCVBKM"
    idx := LetterIndex(StrUpper(letter))
    out := SubStr(colemak, idx + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

QwertzLetter(letter) {
    m := Map("Y","Z", "Z","Y")
    u := StrUpper(letter)
    out := m.Has(u) ? m[u] : u
    return IsUpperLetter(letter) ? out : StrLower(out)
}

KeyboardAdjacentRightLetter(letter) {
    rows := ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
    return KeyboardAdjacent(letter, rows, 1)
}

KeyboardAdjacentLeftLetter(letter) {
    rows := ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
    return KeyboardAdjacent(letter, rows, -1)
}

KeyboardAdjacent(letter, rows, delta) {
    u := StrUpper(letter)
    for _, row in rows {
        pos := InStr(row, u)
        if pos > 0 {
            newPos := PositiveMod(pos - 1 + delta, StrLen(row)) + 1
            out := SubStr(row, newPos, 1)
            return IsUpperLetter(letter) ? out : StrLower(out)
        }
    }
    return letter
}

PhoneT9DigitLetter(letter) {
    u := StrUpper(letter)
    if InStr("ABC", u)
        return "2 "
    if InStr("DEF", u)
        return "3 "
    if InStr("GHI", u)
        return "4 "
    if InStr("JKL", u)
        return "5 "
    if InStr("MNO", u)
        return "6 "
    if InStr("PQRS", u)
        return "7 "
    if InStr("TUV", u)
        return "8 "
    if InStr("WXYZ", u)
        return "9 "
    return letter
}

PhoneMultitapLetter(letter) {
    groups := Map("2", "ABC", "3", "DEF", "4", "GHI", "5", "JKL", "6", "MNO", "7", "PQRS", "8", "TUV", "9", "WXYZ")
    u := StrUpper(letter)
    for digit, group in groups {
        pos := InStr(group, u)
        if pos > 0
            return RepeatText(digit, pos) . " "
    }
    return letter
}

ChessCoordinateLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    files := "ABCDEFGH"
    file := SubStr(files, Mod(idx, 8) + 1, 1)
    rank := Floor(idx / 8) + 1
    return file . rank . " "
}

DicePairCodeLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    return (Floor(idx / 6) + 1) . "-" . (Mod(idx, 6) + 1) . " "
}

DominoTileCodeLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    left := Floor(idx / 7)
    right := Mod(idx, 7)
    code := 0x1F030 + left * 8 + right
    return Chr(code) . " "
}

PlayingCardCodeLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    suits := [0x1F0A0, 0x1F0B0, 0x1F0C0, 0x1F0D0]
    suit := Floor(idx / 13) + 1
    rank := Mod(idx, 13) + 1
    if rank >= 12
        rank += 1 ; skip knight slot in Unicode card block
    return Chr(suits[suit] + rank) . " "
}

Base58IndexLetter(letter) {
    alpha := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    return SubStr(alpha, LetterIndex(StrUpper(letter)) + 1, 1) . " "
}

Base62IndexLetter(letter) {
    alpha := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    return SubStr(alpha, LetterIndex(StrUpper(letter)) + 11, 1) . " "
}

CrockfordBase32IndexLetter(letter) {
    alpha := "0123456789ABCDEFGHJKMNPQRSTVWXYZ"
    return SubStr(alpha, LetterIndex(StrUpper(letter)) + 1, 1) . " "
}

Base85PerLetter(letter) {
    v := Ord(letter)
    high := Floor(v / 85)
    low := Mod(v, 85)
    return Chr(33 + high) . Chr(33 + low) . " "
}

UuencodePerLetter(letter) {
    v := Ord(letter) & 0x3F
    return Chr(v = 0 ? 96 : v + 32) . " "
}

EBCDICHexLetter(letter) {
    u := StrUpper(letter)
    idx := LetterIndex(u)
    if idx < 9
        code := 0xC1 + idx
    else if idx < 18
        code := 0xD1 + (idx - 9)
    else
        code := 0xE2 + (idx - 18)
    if !IsUpperLetter(letter)
        code += 0x40
    return Format("{:02X} ", code)
}

Utf8HexLetter(letter) {
    return Format("{:02X} ", Ord(letter))
}

Utf16LEHexLetter(letter) {
    code := Ord(letter)
    return Format("{:02X} {:02X} ", code & 0xFF, (code >> 8) & 0xFF)
}

HtmlHexEntityLetter(letter) {
    return "&#x" . Format("{:X}", Ord(letter)) . "; "
}

LCGChecksumTokenLetter(letter) {
    ; Lightweight deterministic pseudo-hash token for live typing display.
    code := Ord(letter)
    v := PositiveMod(code * 1103515245 + 12345, 0x1000000)
    return Format("{:06X} ", v)
}

KnuthChecksumTokenLetter(letter) {
    ; Lightweight deterministic pseudo-hash token for live typing display.
    code := Ord(letter)
    v := PositiveMod((code * 2654435761) ^ 0x5A5A5A, 0x1000000)
    return Format("{:06X} ", v)
}

RandomDigitPermutation(length := 9) {
    arr := []
    Loop length
        arr.Push(A_Index . "")
    i := arr.Length
    while i > 1 {
        j := Random(1, i)
        tmp := arr[i]
        arr[i] := arr[j]
        arr[j] := tmp
        i -= 1
    }
    out := ""
    for _, ch in arr
        out .= ch
    return out
}


; ------------------------------------------------------------
; Real-world and historical live/block ciphers added in v7
; ------------------------------------------------------------

RailFenceBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "Rail")
}

ScytaleBlockLetter(letter) {
    return BlockCipherLetter(letter, 8, "Scytale")
}


RagbabyLetter(letter) {
    global keyText, streamIndex
    alpha := KeywordAlphabet(keyText)
    u := StrUpper(letter)
    idx := InStr(alpha, u) - 1
    if idx < 0
        return letter
    shift := streamIndex + 2
    streamIndex += 1
    mapped := SubStr(alpha, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

ClaveLetter(letter) {
    global keyText, streamIndex
    alpha := KeywordAlphabet("CIPHER")
    cleanKey := CleanLetters(keyText)
    if cleanKey = ""
        cleanKey := "CLAVE"
    u := StrUpper(letter)
    p := InStr(alpha, u) - 1
    if p < 0
        return letter
    kch := SubStr(cleanKey, PositiveMod(streamIndex, StrLen(cleanKey)) + 1, 1)
    k := InStr(alpha, kch) - 1
    streamIndex += 1
    mapped := SubStr(alpha, PositiveMod(p + k, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

GromarkLetter(letter) {
    global keyText, streamIndex
    alpha := KeywordAlphabet(keyText)
    shift := GromarkDigitAt(streamIndex)
    streamIndex += 1
    idx := LetterIndex(StrUpper(letter))
    mapped := SubStr(alpha, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

GromarkDigitAt(index) {
    global keyText
    digits := CleanDigits(keyText)
    if digits = ""
        digits := "12345"
    arr := []
    for _, ch in StrSplit(digits)
        arr.Push(ch + 0)
    while arr.Length <= index {
        n := PositiveMod(arr[arr.Length] + arr[arr.Length - 1], 10)
        arr.Push(n)
    }
    return arr[index + 1]
}

SeriatedPlayfairLetter(letter) {
    return PlayfairLetter(letter)
}

Playfair6x6Letter(letter) {
    return GenericPairLetter(letter, "Playfair6")
}

TwoSquareVerticalLetter(letter) {
    return GenericPairLetter(letter, "TwoSquareV")
}

TriSquareLetter(letter) {
    return GenericPairLetter(letter, "TriSquare")
}

TwoSquare6x6Letter(letter) {
    return GenericPairLetter(letter, "TwoSquare6")
}

FourSquare6x6Letter(letter) {
    return GenericPairLetter(letter, "FourSquare6")
}

Bifid6x6Letter(letter) {
    return GenericPairLetter(letter, "Bifid6")
}

GenericPairLetter(letter, kind) {
    global pairBuffer
    u := StrUpper(letter)
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    switch kind {
        case "Playfair6":
            return Playfair6x6EncryptPair(a, b, IsUpperLetter(letter))
        case "TwoSquareV":
            return TwoSquareVerticalEncryptPair(a, b, IsUpperLetter(letter))
        case "TriSquare":
            return TriSquareEncryptPair(a, b, IsUpperLetter(letter))
        case "TwoSquare6":
            return TwoSquare6x6EncryptPair(a, b, IsUpperLetter(letter))
        case "FourSquare6":
            return FourSquare6x6EncryptPair(a, b, IsUpperLetter(letter))
        case "Bifid6":
            return Bifid6x6EncryptPair(a, b, IsUpperLetter(letter))
    }
    return a . b
}

Square6(key) {
    base := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    clean := RegExReplace(StrUpper(key), "[^A-Z0-9]", "")
    out := ""
    for _, ch in StrSplit(clean . base) {
        if !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 36)
}

Playfair6x6EncryptPair(a, b, uppercase := true) {
    global keyText
    sq := Square6(keyText)
    ia := InStr(sq, a) - 1
    ib := InStr(sq, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 6), ca := Mod(ia, 6)
    rb := Floor(ib / 6), cb := Mod(ib, 6)
    if ra = rb {
        c1 := SubStr(sq, ra * 6 + Mod(ca + 1, 6) + 1, 1)
        c2 := SubStr(sq, rb * 6 + Mod(cb + 1, 6) + 1, 1)
    } else if ca = cb {
        c1 := SubStr(sq, Mod(ra + 1, 6) * 6 + ca + 1, 1)
        c2 := SubStr(sq, Mod(rb + 1, 6) * 6 + cb + 1, 1)
    } else {
        c1 := SubStr(sq, ra * 6 + cb + 1, 1)
        c2 := SubStr(sq, rb * 6 + ca + 1, 1)
    }
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

TwoSquareVerticalEncryptPair(a, b, uppercase := true) {
    global keyText
    top := PlayfairSquare(keyText)
    bottom := PlayfairSquare("VERTICAL" . keyText)
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    ia := InStr(top, a) - 1
    ib := InStr(bottom, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    if ca = cb {
        c1 := SubStr(top, Mod(ra + 1, 5) * 5 + ca + 1, 1)
        c2 := SubStr(bottom, Mod(rb + 1, 5) * 5 + cb + 1, 1)
    } else {
        c1 := SubStr(top, ra * 5 + cb + 1, 1)
        c2 := SubStr(bottom, rb * 5 + ca + 1, 1)
    }
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

TriSquareEncryptPair(a, b, uppercase := true) {
    global keyText
    normal := "ABCDEFGHIKLMNOPQRSTUVWXYZ"
    s1 := PlayfairSquare(keyText)
    s2 := PlayfairSquare("BRAVO" . keyText)
    s3 := PlayfairSquare("CHARLIE" . keyText)
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    ia := InStr(normal, a) - 1
    ib := InStr(normal, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    c1 := SubStr(s1, ra * 5 + cb + 1, 1)
    c2 := SubStr(s2, rb * 5 + ca + 1, 1)
    c3 := SubStr(s3, ra * 5 + ca + 1, 1)
    out := c1 . c2 . c3
    return uppercase ? out : StrLower(out)
}

TwoSquare6x6EncryptPair(a, b, uppercase := true) {
    global keyText
    left := Square6(keyText)
    right := Square6("SQUARE" . keyText)
    ia := InStr(left, a) - 1
    ib := InStr(right, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 6), ca := Mod(ia, 6)
    rb := Floor(ib / 6), cb := Mod(ib, 6)
    c1 := SubStr(right, ra * 6 + cb + 1, 1)
    c2 := SubStr(left, rb * 6 + ca + 1, 1)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

FourSquare6x6EncryptPair(a, b, uppercase := true) {
    global keyText
    normal := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    tr := Square6(keyText)
    bl := Square6("FOUR" . keyText)
    ia := InStr(normal, a) - 1
    ib := InStr(normal, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 6), ca := Mod(ia, 6)
    rb := Floor(ib / 6), cb := Mod(ib, 6)
    c1 := SubStr(tr, ra * 6 + cb + 1, 1)
    c2 := SubStr(bl, rb * 6 + ca + 1, 1)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

Bifid6x6EncryptPair(a, b, uppercase := true) {
    global keyText
    sq := Square6(keyText)
    ia := InStr(sq, a) - 1
    ib := InStr(sq, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 6), ca := Mod(ia, 6)
    rb := Floor(ib / 6), cb := Mod(ib, 6)
    c1 := SubStr(sq, ra * 6 + rb + 1, 1)
    c2 := SubStr(sq, ca * 6 + cb + 1, 1)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

Hill3x3BlockLetter(letter) {
    return BlockCipherLetter(letter, 3, "Hill3")
}

NicodemusBlockLetter(letter) {
    return BlockCipherLetter(letter, 12, "Nicodemus")
}

CadenusBlockLetter(letter) {
    return BlockCipherLetter(letter, 25, "Cadenus")
}

AMSCOBlockLetter(letter) {
    return BlockCipherLetter(letter, 12, "AMSCO")
}

SwagmanBlockLetter(letter) {
    return BlockCipherLetter(letter, 8, "Swagman")
}

BazeriesBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "Bazeries")
}

DisruptedBlockLetter(letter) {
    return BlockCipherLetter(letter, 12, "Disrupted")
}

IncompleteColumnarBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "IncompleteColumnar")
}

CompleteColumnarBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "CompleteColumnar")
}

AlternatingColumnarBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "AlternatingColumnar")
}

BoustrophedonRouteBlockLetter(letter) {
    return BlockCipherLetter(letter, RouteBlockSize(), "Boustrophedon")
}

SpiralInwardRouteBlockLetter(letter) {
    return BlockCipherLetter(letter, RouteBlockSize(), "SpiralIn")
}

SpiralOutwardRouteBlockLetter(letter) {
    return BlockCipherLetter(letter, RouteBlockSize(), "SpiralOut")
}

ReadingOrderRouteBlockLetter(letter) {
    return BlockCipherLetter(letter, RouteBlockSize(), "ReadingRoute")
}

RotatingSquareRouteBlockLetter(letter) {
    return BlockCipherLetter(letter, RouteBlockSize(), "RotatingSquare")
}

GrilleMaskBlockLetter(letter) {
    return BlockCipherLetter(letter, 25, "GrilleMask")
}

FleissnerGrilleBlockLetter(letter) {
    return BlockCipherLetter(letter, 16, "Fleissner")
}

HomophonicSubstitutionLetter(letter) {
    pools := Map(
        "E", ["00","01","02","03"], "T", ["04","05","06"], "A", ["07","08","09"],
        "O", ["10","11","12"], "I", ["13","14"], "N", ["15","16"], "S", ["17","18"],
        "H", ["19","20"], "R", ["21","22"], "D", ["23","24"], "L", ["25","26"],
        "C", ["27","28"], "U", ["29","30"], "M", ["31","32"], "W", ["33","34"],
        "F", ["35"], "G", ["36"], "Y", ["37"], "P", ["38"], "B", ["39"], "V", ["40"],
        "K", ["41"], "J", ["42"], "X", ["43"], "Q", ["44"], "Z", ["45"]
    )
    u := StrUpper(letter)
    if !pools.Has(u)
        return letter
    pool := pools[u]
    return pool[Random(1, pool.Length)] . " "
}

ADFGVXEscapedLetter(letter) {
    global keyText
    hex := Format("{:02X}", Ord(letter))
    return KeyedADFGVXChar(SubStr(hex,1,1), keyText) . KeyedADFGVXChar(SubStr(hex,2,1), keyText) . " "
}

KeyedADFGVXChar(ch, key) {
    labels := "ADFGVX"
    sq := Square6(key)
    idx := InStr(sq, StrUpper(ch)) - 1
    if idx < 0
        return ch
    row := Floor(idx / 6) + 1
    col := Mod(idx, 6) + 1
    return SubStr(labels, row, 1) . SubStr(labels, col, 1)
}

Base45Letter(letter) {
    alpha := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
    b := Ord(letter)
    return SubStr(alpha, Mod(b,45)+1,1) . SubStr(alpha, Floor(b/45)+1,1) . " "
}

Base36Letter(letter) {
    alpha := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    n := Ord(letter)
    if n = 0
        return "0 "
    out := ""
    while n > 0 {
        r := Mod(n, 36)
        out := SubStr(alpha, r + 1, 1) . out
        n := Floor(n / 36)
    }
    return out . " "
}

Base92Letter(letter) {
    alpha := "!#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[]^_``abcdefghijklmnopqrstuvwxyz{|}~"
    n := Ord(letter)
    out := ""
    while n > 0 {
        r := Mod(n, StrLen(alpha))
        out := SubStr(alpha, r + 1, 1) . out
        n := Floor(n / StrLen(alpha))
    }
    return out . " "
}

Z85Letter(letter) {
    alpha := "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ.-:+=^!/*?&<>()[]{}@%$#"
    n := Ord(letter)
    out := ""
    while n > 0 {
        r := Mod(n, 85)
        out := SubStr(alpha, r + 1, 1) . out
        n := Floor(n / 85)
    }
    return out . " "
}

Hill3Transform(block) {
    nums := [6,24,1,13,16,10,20,17,15]
    out := ""
    block := PadRight(block, 3, "X")
    Loop 3 {
        row := A_Index - 1
        sum := 0
        Loop 3 {
            col := A_Index - 1
            sum += nums[row * 3 + col + 1] * LetterIndex(SubStr(block, col + 1, 1))
        }
        out .= LetterFromIndex(PositiveMod(sum, 26), true)
    }
    return out
}

NicodemusTransform(block, key) {
    mixed := ""
    cleanKey := CleanLetters(key)
    if cleanKey = ""
        cleanKey := "KEY"
    for i, ch in StrSplit(block) {
        shift := KeyShiftAt(cleanKey, i - 1)
        mixed .= LetterFromIndex(PositiveMod(LetterIndex(ch) + shift, 26), true)
    }
    return ColumnarTransform(mixed, cleanKey)
}

CadenusTransform(block, key) {
    return ColumnarTransform(block, key)
}

AMSCOTransform(block, key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "CIPHER"
    cols := StrLen(clean)
    lengths := []
    total := 0
    toggle := 1
    while total < StrLen(block) {
        row := []
        Loop cols {
            take := toggle = 1 ? 1 : 2
            if total + take > StrLen(block)
                take := StrLen(block) - total
            row.Push(take)
            total += take
            toggle := toggle = 1 ? 2 : 1
            if total >= StrLen(block)
                break
        }
        lengths.Push(row)
    }
    cells := []
    idx := 1
    for _, row in lengths {
        cRow := []
        for _, n in row {
            cRow.Push(SubStr(block, idx, n))
            idx += n
        }
        cells.Push(cRow)
    }
    out := ""
    for _, cRaw in ColumnOrder(clean) {
        c := Integer(cRaw)
        for _, row in cells {
            if c <= row.Length
                out .= row[c]
        }
    }
    return out
}

SwagmanTransform(block, key) {
    digits := CleanDigits(key)
    if digits = ""
        digits := "3142"
    width := Integer(StrLen(digits))
    block := PadRight(block, Integer(Ceil(StrLen(block)/width)*width), "X")
    order := []
    Loop width
        order.Push(A_Index)
    i := 1
    while i <= order.Length {
        j := i + 1
        while j <= order.Length {
            dj := Integer(SubStr(digits, order[j], 1))
            di := Integer(SubStr(digits, order[i], 1))
            if (dj < di) {
                tmp := order[i]
                order[i] := order[j]
                order[j] := tmp
            }
            j += 1
        }
        i += 1
    }
    out := ""
    off := 1
    while off <= StrLen(block) {
        chunkText := SubStr(block, off, width)
        for _, pos in order
            out .= SubStr(chunkText, pos, 1)
        off += width
    }
    return out
}

BazeriesTransform(block, number, key) {
    alpha := KeywordAlphabet(key)
    subbed := ""
    for _, ch in StrSplit(block)
        subbed .= SubstituteFromAlphabet(ch, alpha)
    digits := CleanDigits(number)
    if digits = ""
        digits := "31415"
    out := ""
    idx := 1
    di := 1
    while idx <= StrLen(subbed) {
        size := SubStr(digits, di, 1) + 0
        if size < 1
            size := 1
        out .= ReverseText(SubStr(subbed, idx, size))
        idx += size
        di := di >= StrLen(digits) ? 1 : di + 1
    }
    return out
}

ReverseText(text) {
    out := ""
    Loop StrLen(text)
        out := SubStr(text, A_Index, 1) . out
    return out
}

DisruptedTransform(block, key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "DISRUPT"
    cols := Integer(StrLen(clean))
    rows := Integer(Ceil(StrLen(block) / cols))
    block := PadRight(block, rows * cols, "X")
    shifted := ""
    Loop rows {
        r := A_Index
        row := SubStr(block, (r - 1) * cols + 1, cols)
        sh := Mod(r - 1, cols)
        shifted .= SubStr(row, sh + 1) . SubStr(row, 1, sh)
    }
    return ColumnarTransform(shifted, clean)
}

IncompleteColumnarTransform(block, key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "CIPHER"
    cols := Integer(StrLen(clean))
    rows := Integer(Ceil(StrLen(block) / cols))
    out := ""
    for _, cRaw in ColumnOrder(clean) {
        c := Integer(cRaw)
        Loop rows {
            pos := ((A_Index - 1) * cols) + c
            if pos <= StrLen(block)
                out .= SubStr(block, pos, 1)
        }
    }
    return out
}

AlternatingColumnarTransform(block, key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "CIPHER"
    cols := Integer(StrLen(clean))
    rows := Integer(Ceil(StrLen(block) / cols))
    block := PadRight(block, rows * cols, "X")
    out := ""
    n := 0
    for _, cRaw in ColumnOrder(clean) {
        c := Integer(cRaw)
        if Mod(n, 2) = 0 {
            r := 1
            while r <= rows {
                out .= SubStr(block, (r - 1) * cols + c, 1)
                r += 1
            }
        } else {
            r := rows
            while r >= 1 {
                out .= SubStr(block, (r - 1) * cols + c, 1)
                r -= 1
            }
        }
        n += 1
    }
    return out
}

BoustrophedonRouteTransform(block, side) {
    side := Integer(Max(2, Min(5, ToIntegerOrDefault(side, 3))))
    block := PadRight(block, side * side, "X")
    out := ""
    Loop side {
        r := A_Index
        row := SubStr(block, (r - 1) * side + 1, side)
        out .= Mod(r,2) ? row : ReverseText(row)
    }
    return out
}

SpiralOutTransform(block, side) {
    inside := RouteSpiralTransform(block, side)
    return ReverseText(inside)
}

ReadingRouteTransform(block, side, key) {
    side := Integer(Max(2, Min(5, ToIntegerOrDefault(side, 3))))
    if InStr(StrLower(key), "snake")
        return BoustrophedonRouteTransform(block, side)
    block := PadRight(block, side * side, "X")
    out := ""
    Loop side {
        c := A_Index
        Loop side
            out .= GridChar(block, side, A_Index, c)
    }
    return out
}

RotatingSquareTransform(block, side, turns) {
    side := Integer(Max(2, Min(5, ToIntegerOrDefault(side, 3))))
    turns := PositiveMod(ToIntegerOrDefault(turns, 1), 4)
    block := PadRight(block, side * side, "X")
    out := ""
    Loop side {
        r := A_Index
        Loop side {
            c := A_Index
            rr := r, cc := c
            if turns = 1 {
                rr := side - c + 1, cc := r
            } else if turns = 2 {
                rr := side - r + 1, cc := side - c + 1
            } else if turns = 3 {
                rr := c, cc := side - r + 1
            }
            out .= GridChar(block, side, rr, cc)
        }
    }
    return out
}

GrilleMaskTransform(block) {
    side := 5
    block := PadRight(block, 25, "X")
    positions := [1,7,13,19,25]
    out := ""
    for _, pos in positions
        out .= SubStr(block, pos, 1)
    Loop 25 {
        if !ArrayHasValue(positions, A_Index)
            out .= SubStr(block, A_Index, 1)
    }
    return out
}

FleissnerTransform(block) {
    block := PadRight(block, 16, "X")
    order := [1,2,8,12,4,7,10,13,5,9,11,16,3,6,14,15]
    out := ""
    for _, pos in order
        out .= SubStr(block, pos, 1)
    return out
}

ColumnarBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "Columnar")
}

DoubleColumnarBlockLetter(letter) {
    return BlockCipherLetter(letter, 12, "DoubleColumnar")
}

RouteCipherBlockLetter(letter) {
    return BlockCipherLetter(letter, RouteBlockSize(), "Route")
}

MyszkowskiBlockLetter(letter) {
    return BlockCipherLetter(letter, 12, "Myszkowski")
}

BifidFullPeriodLetter(letter) {
    return BlockCipherLetter(letter, 10, "BifidFull")
}

TrifidFullPeriodLetter(letter) {
    return BlockCipherLetter(letter, 9, "TrifidFull")
}

BlockCipherLetter(letter, blockSize, kind) {
    global pairBuffer
    blockSize := ToIntegerOrDefault(blockSize, 1)
    pairBuffer .= StrUpper(letter)
    if StrLen(pairBuffer) < blockSize
        return ""
    block := pairBuffer
    pairBuffer := ""
    return EncryptNamedBlock(block, kind) . " "
}

EncryptNamedBlock(block, kind) {
    global keyText, shiftValue
    switch kind {
        case "Rail":
            return RailFenceBlockTransform(block, Max(2, Min(8, shiftValue)))
        case "Scytale":
            return ScytaleTransform(block, Max(2, Min(10, shiftValue)))
        case "Columnar":
            return ColumnarTransform(block, keyText)
        case "DoubleColumnar":
            return ColumnarTransform(ColumnarTransform(block, keyText), ReverseString(CleanLetters(keyText) = "" ? "KEY" : CleanLetters(keyText)))
        case "Route":
            return RouteSpiralTransform(block, RouteBlockSide())
        case "Myszkowski":
            return MyszkowskiTransform(block, keyText)
        case "BifidFull":
            return BifidFullTransform(block, keyText)
        case "TrifidFull":
            return TrifidFullTransform(block, keyText)
        case "Hill3":
            return Hill3Transform(block)
        case "Nicodemus":
            return NicodemusTransform(block, keyText)
        case "Cadenus":
            return CadenusTransform(block, keyText)
        case "AMSCO":
            return AMSCOTransform(block, keyText)
        case "Swagman":
            return SwagmanTransform(block, keyText)
        case "Bazeries":
            return BazeriesTransform(block, shiftValue, keyText)
        case "Disrupted":
            return DisruptedTransform(block, keyText)
        case "IncompleteColumnar":
            return IncompleteColumnarTransform(block, keyText)
        case "CompleteColumnar":
            return ColumnarTransform(block, keyText)
        case "AlternatingColumnar":
            return AlternatingColumnarTransform(block, keyText)
        case "Boustrophedon":
            return BoustrophedonRouteTransform(block, RouteBlockSide())
        case "SpiralIn":
            return RouteSpiralTransform(block, RouteBlockSide())
        case "SpiralOut":
            return SpiralOutTransform(block, RouteBlockSide())
        case "ReadingRoute":
            return ReadingRouteTransform(block, RouteBlockSide(), keyText)
        case "RotatingSquare":
            return RotatingSquareTransform(block, RouteBlockSide(), shiftValue)
        case "GrilleMask":
            return GrilleMaskTransform(block)
        case "Fleissner":
            return FleissnerTransform(block)
        case "Redefence":
            return RedefenceTransform(block, Max(2, Min(8, shiftValue)), 1)
        case "PolybiusColumnar":
            return ColumnarTransform(PolybiusFractionText(block, keyText), keyText)
    }
    return block
}

RouteBlockSide() {
    global shiftValue
    n := ToIntegerOrDefault(shiftValue, 3)
    return n >= 4 ? 4 : 3
}

RouteBlockSize() {
    side := RouteBlockSide()
    return side * side
}

PadRight(text, length, pad := "X") {
    length := ToIntegerOrDefault(length, StrLen(text))
    while StrLen(text) < length
        text .= pad
    return SubStr(text, 1, length)
}


RailFenceBlockTransform(block, rails := 3) {
    rails := Max(2, Min(8, rails))
    rows := []
    Loop rails
        rows.Push("")
    r := 1
    dir := 1
    for _, ch in StrSplit(block) {
        rows[r] .= ch
        if r = rails
            dir := -1
        else if r = 1
            dir := 1
        r += dir
    }
    out := ""
    for _, row in rows
        out .= row
    return out
}

ScytaleTransform(block, cols := 4) {
    cols := Integer(Max(2, Min(10, ToIntegerOrDefault(cols, 4))))
    rows := Integer(Ceil(StrLen(block) / cols))
    block := PadRight(block, rows * cols, "X")
    out := ""
    Loop cols {
        c := A_Index
        Loop rows {
            pos := (A_Index - 1) * cols + c
            out .= SubStr(block, pos, 1)
        }
    }
    return out
}

ColumnOrder(key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "KEY"
    order := []
    count := Integer(StrLen(clean))
    Loop count
        order.Push(Integer(A_Index))
    i := 1
    while i <= order.Length {
        j := i + 1
        while j <= order.Length {
            oi := Integer(order[i])
            oj := Integer(order[j])
            a := SubStr(clean, oi, 1)
            b := SubStr(clean, oj, 1)
            ao := Ord(a)
            bo := Ord(b)
            if (bo < ao) || (bo = ao && oj < oi) {
                tmp := order[i]
                order[i] := order[j]
                order[j] := tmp
            }
            j += 1
        }
        i += 1
    }
    return order
}

ColumnarTransform(block, key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "KEY"
    cols := Integer(StrLen(clean))
    rows := Integer(Ceil(StrLen(block) / cols))
    block := PadRight(block, rows * cols, "X")
    order := ColumnOrder(clean)
    out := ""
    for _, cRaw in order {
        c := Integer(cRaw)
        Loop rows {
            pos := ((A_Index - 1) * cols) + c
            out .= SubStr(block, pos, 1)
        }
    }
    return out
}

MyszkowskiTransform(block, key) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "BALLOON"
    cols := Integer(StrLen(clean))
    rows := Integer(Ceil(StrLen(block) / cols))
    block := PadRight(block, rows * cols, "X")
    letters := []
    for _, ch in StrSplit(clean) {
        if !ArrayHasValue(letters, ch)
            letters.Push(ch)
    }
    ; Sort unique key letters.
    i := 1
    while i <= letters.Length {
        j := i + 1
        while j <= letters.Length {
            aj := Ord(letters[j])
            ai := Ord(letters[i])
            if (aj < ai) {
                tmp := letters[i]
                letters[i] := letters[j]
                letters[j] := tmp
            }
            j += 1
        }
        i += 1
    }
    out := ""
    for _, keyCh in letters {
        colsForCh := []
        Loop cols {
            if SubStr(clean, A_Index, 1) = keyCh
                colsForCh.Push(A_Index)
        }
        if colsForCh.Length = 1 {
            c := Integer(colsForCh[1])
            Loop rows {
                pos := ((A_Index - 1) * cols) + c
                out .= SubStr(block, pos, 1)
            }
        } else {
            Loop rows {
                r := A_Index
                for _, cRaw in colsForCh {
                    c := Integer(cRaw)
                    pos := ((r - 1) * cols) + c
                    out .= SubStr(block, pos, 1)
                }
            }
        }
    }
    return out
}

RouteSpiralTransform(block, side := 3) {
    side := Integer(Max(2, Min(5, ToIntegerOrDefault(side, 3))))
    block := PadRight(block, side * side, "X")
    left := 1
    right := side
    top := 1
    bottom := side
    out := ""
    while left <= right && top <= bottom {
        c := left
        while c <= right {
            out .= GridChar(block, side, top, c)
            c += 1
        }
        top += 1
        r := top
        while r <= bottom {
            out .= GridChar(block, side, r, right)
            r += 1
        }
        right -= 1
        if top <= bottom {
            c := right
            while c >= left {
                out .= GridChar(block, side, bottom, c)
                c -= 1
            }
            bottom -= 1
        }
        if left <= right {
            r := bottom
            while r >= top {
                out .= GridChar(block, side, r, left)
                r -= 1
            }
            left += 1
        }
    }
    return out
}

GridChar(block, side, row, col) {
    return SubStr(block, (row - 1) * side + col, 1)
}

ArrayHasValue(arr, value) {
    for _, v in arr {
        if v = value
            return true
    }
    return false
}

BifidFullTransform(block, key) {
    square := PlayfairSquare(key)
    coords := ""
    for _, rawCh in StrSplit(block) {
        ch := rawCh = "J" ? "I" : rawCh
        idx := InStr(square, ch) - 1
        coords .= (Floor(idx / 5) + 1) . (Mod(idx, 5) + 1)
    }
    out := ""
    i := 1
    while i < StrLen(coords) {
        r := SubStr(coords, i, 1) + 0
        c := SubStr(coords, i + 1, 1) + 0
        out .= SubStr(square, (r - 1) * 5 + c, 1)
        i += 2
    }
    return out
}

TrifidFullTransform(block, key) {
    alpha := KeywordAlphabet(key . "ABCDEFGHIJKLMNOPQRSTUVWXYZ") . "."
    alpha := SubStr(alpha, 1, 27)
    coords := ""
    for _, rawCh in StrSplit(block) {
        ch := rawCh = "J" ? "I" : rawCh
        idx := InStr(alpha, ch) - 1
        if idx < 0
            idx := 26
        layer := Floor(idx / 9) + 1
        rem := Mod(idx, 9)
        row := Floor(rem / 3) + 1
        col := Mod(rem, 3) + 1
        coords .= layer . row . col
    }
    out := ""
    i := 1
    while i + 2 <= StrLen(coords) {
        layer := SubStr(coords, i, 1) + 0
        row := SubStr(coords, i + 1, 1) + 0
        col := SubStr(coords, i + 2, 1) + 0
        idx := (layer - 1) * 9 + (row - 1) * 3 + col
        out .= SubStr(alpha, idx, 1)
        i += 3
    }
    return out
}

JeffersonDiskLetter(letter) {
    global streamIndex, keyText
    disks := CylinderDisks("Jefferson")
    disk := disks[PositiveMod(streamIndex, disks.Length) + 1]
    idx := InStr(disk, StrUpper(letter)) - 1
    shift := KeyShiftAt(keyText, streamIndex) + 1
    streamIndex += 1
    mapped := SubStr(disk, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

M94CylinderLetter(letter) {
    global streamIndex, keyText
    disks := CylinderDisks("M94")
    disk := disks[PositiveMod(streamIndex, disks.Length) + 1]
    idx := InStr(disk, StrUpper(letter)) - 1
    shift := KeyShiftAt(keyText, streamIndex) + 2
    streamIndex += 1
    mapped := SubStr(disk, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

BazeriesCylinderLetter(letter) {
    global streamIndex, keyText
    disks := CylinderDisks("Bazeries")
    disk := disks[PositiveMod(streamIndex, disks.Length) + 1]
    idx := InStr(disk, StrUpper(letter)) - 1
    shift := 26 - (KeyShiftAt(keyText, streamIndex) + 1)
    streamIndex += 1
    mapped := SubStr(disk, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

CylinderDisks(kind) {
    if kind = "M94" {
        words := ["ARMY", "SIGNAL", "CORPS", "RADIO", "FIELD", "CAMP", "FORT", "EAGLE", "LIBERTY", "CIPHER", "WIRE", "MARCH", "HORSE", "RIVER", "BRIDGE", "CANNON", "PATROL", "SCOUT", "GUARD", "ORDER", "BUGLE", "NATION", "VICTORY", "BATTLE", "COMMAND"]
    } else if kind = "Bazeries" {
        words := ["BAZERIES", "FRANCE", "PARIS", "MARINE", "ARMEE", "SECRET", "DIPLOMAT", "COURIER", "NAPOLEON", "CITADEL", "REPUBLIC", "MINISTER", "GENERAL", "BUREAU", "CAVALRY", "ARTILLERY", "FORTRESS", "TELEGRAPH", "CODEBOOK", "MESSAGE"]
    } else {
        words := ["JEFFERSON", "MONTICELLO", "VIRGINIA", "PRESIDENT", "LIBERTY", "REPUBLIC", "CIPHER", "WHEEL", "DIPLOMACY", "CONGRESS", "SECRET", "LETTER", "FEDERAL", "TREATY", "COLONY", "ATLANTIC", "CABINET", "EMBASSY", "COURIER", "ARCHIVE", "PHILADELPHIA", "DECLARATION", "REVOLUTION", "CAPITOL", "UNION", "AMERICA"]
    }
    disks := []
    for _, word in words
        disks.Push(KeywordAlphabet(word))
    return disks
}

M209HagelinLetter(letter) {
    global streamIndex, shiftValue
    ; Hagelin M-209 inspired live stream: six irregular wheels produce a shifting value.
    wheelLens := [26, 25, 23, 21, 19, 17]
    pins := ["ABDHIKMNSTVW", "ADEGJKLORSUX", "ABGHJLMNQRS", "CEFHIMNPSTU", "BDEGILMRT", "ACFGHJPQ"]
    count := 0
    for i, wheelLen in wheelLens {
        pos := PositiveMod(streamIndex + shiftValue + i, wheelLen)
        letterAt := SubStr("ABCDEFGHIJKLMNOPQRSTUVWXYZ", PositiveMod(pos, 26) + 1, 1)
        if InStr(pins[i], letterAt)
            count += i
    }
    streamIndex += 1
    return ShiftLetter(letter, -count)
}

VICCheckerboardLetter(letter) {
    global keyText
    order := KeywordAlphabet(keyText . "ETAOINSHRDLCUMWFGYPBVKJXQZ")
    return CheckerboardNumberLetterWithOrder(letter, "28", order)
}

CheckerboardNumberLetterWithOrder(letter, rowDigits, order) {
    u := StrUpper(letter)
    pos := InStr(order, u)
    if pos <= 0
        return letter
    rd1 := SubStr(rowDigits, 1, 1)
    rd2 := SubStr(rowDigits, 2, 1)
    topDigits := []
    Loop 10 {
        d := A_Index - 1
        ds := d . ""
        if ds != rd1 && ds != rd2
            topDigits.Push(ds)
    }
    if pos <= 8
        return topDigits[pos] . " "
    pos2 := pos - 9
    row := Floor(pos2 / 10)
    col := Mod(pos2, 10)
    return (row = 0 ? rd1 : rd2) . col . " "
}

OneTimePadLetter(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

VernamXor5BitLetter(letter) {
    global keyText, streamIndex
    x := LetterIndex(StrUpper(letter))
    k := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    y := PositiveMod((x ^ k), 26)
    return LetterFromIndex(y, IsUpperLetter(letter))
}

NihilistNumericStreamLetter(letter) {
    global keyText, streamIndex
    cleanKey := CleanLetters(keyText)
    if cleanKey = ""
        cleanKey := "KEY"
    square := KeywordAlphabet(cleanKey)
    p := PolybiusNumberFor(StrUpper(letter), square)
    kch := SubStr(cleanKey, PositiveMod(streamIndex, StrLen(cleanKey)) + 1, 1)
    kval := PolybiusNumberFor(kch, square)
    streamIndex += 1
    return (p + kval) . " "
}

PolybiusNumberFor(ch, square) {
    if ch = "J"
        ch := "I"
    square := StrReplace(square, "J", "")
    square := SubStr(square . "ABCDEFGHIKLMNOPQRSTUVWXYZ", 1, 25)
    idx := InStr(square, ch) - 1
    if idx < 0
        return 0
    return (Floor(idx / 5) + 1) * 10 + (Mod(idx, 5) + 1)
}

BookCipherIndexLetter(letter) {
    global keyText, streamIndex
    words := ExtractBookWords(keyText)
    target := StrUpper(letter)
    start := PositiveMod(streamIndex, words.Length) + 1
    i := start
    Loop words.Length {
        word := words[i]
        if SubStr(word, 1, 1) = target {
            streamIndex += 1
            return i . " "
        }
        i += 1
        if i > words.Length
            i := 1
    }
    streamIndex += 1
    return "0" . target . " "
}

ExtractBookWords(text) {
    defaultBook := "ALPHA BRAVO CHARLIE DELTA ECHO FOXTROT GOLF HOTEL INDIA JULIET KILO LIMA MIKE NOVEMBER OSCAR PAPA QUEBEC ROMEO SIERRA TANGO UNIFORM VICTOR WHISKEY XRAY YANKEE ZULU"
    s := CleanLettersWithSpaces(text)
    if Trim(s) = ""
        s := defaultBook
    arr := StrSplit(s, " ")
    out := []
    for _, w in arr {
        if w != ""
            out.Push(w)
    }
    if out.Length = 0
        out := StrSplit(defaultBook, " ")
    return out
}

CleanLettersWithSpaces(text) {
    s := StrUpper(text)
    s := RegExReplace(s, "[^A-Z]+", " ")
    return Trim(s)
}

InitRC4(key) {
    global rc4S, rc4I, rc4J
    rc4S := []
    Loop 256
        rc4S.Push(A_Index - 1)
    if key = ""
        key := "KEY"
    j := 0
    Loop 256 {
        i := A_Index
        kval := Ord(SubStr(key, PositiveMod(i - 1, StrLen(key)) + 1, 1))
        j := PositiveMod(j + rc4S[i] + kval, 256)
        SwapArrayValues(rc4S, i, j + 1)
    }
    rc4I := 0
    rc4J := 0
}

RC4NextByte() {
    global rc4S, rc4I, rc4J
    if rc4S.Length != 256
        InitRC4("KEY")
    rc4I := PositiveMod(rc4I + 1, 256)
    i := rc4I + 1
    rc4J := PositiveMod(rc4J + rc4S[i], 256)
    j := rc4J + 1
    SwapArrayValues(rc4S, i, j)
    idx := PositiveMod(rc4S[i] + rc4S[j], 256) + 1
    return rc4S[idx]
}

RC4HexStreamLetter(letter) {
    k := RC4NextByte()
    return Format("{:02X} ", Ord(letter) ^ k)
}

SwapArrayValues(arr, i, j) {
    tmp := arr[i]
    arr[i] := arr[j]
    arr[j] := tmp
}

InitSolitaireDeck(key := "") {
    global solitaireDeck
    solitaireDeck := []
    Loop 54
        solitaireDeck.Push(A_Index)
    clean := CleanLetters(key)
    for _, ch in StrSplit(clean) {
        SolitaireNextKey()
        SolitaireCountCut(LetterIndex(ch) + 1)
    }
}

SolitairePontifexLetter(letter) {
    k := SolitaireNextKey()
    return ShiftLetter(letter, k)
}

SolitaireNextKey() {
    global solitaireDeck
    if solitaireDeck.Length != 54
        InitSolitaireDeck("")
    Loop {
        SolitaireMoveCard(53, 1)
        SolitaireMoveCard(54, 2)
        SolitaireTripleCut()
        bottom := solitaireDeck[54]
        count := bottom >= 53 ? 53 : bottom
        SolitaireCountCut(count)
        top := solitaireDeck[1]
        idx := top >= 53 ? 53 : top
        outCard := solitaireDeck[idx + 1]
        if outCard < 53
            return PositiveMod(outCard - 1, 26) + 1
    }
}

SolitaireMoveCard(card, steps) {
    global solitaireDeck
    idx := 0
    for i, v in solitaireDeck {
        if v = card {
            idx := i
            break
        }
    }
    if idx = 0
        return
    solitaireDeck.RemoveAt(idx)
    newIdx := idx + steps
    while newIdx > solitaireDeck.Length
        newIdx -= solitaireDeck.Length
    if newIdx = 0
        newIdx := solitaireDeck.Length
    solitaireDeck.InsertAt(newIdx, card)
}

SolitaireTripleCut() {
    global solitaireDeck
    a := 0
    b := 0
    for i, v in solitaireDeck {
        if v >= 53 {
            if a = 0
                a := i
            else {
                b := i
                break
            }
        }
    }
    if a = 0 || b = 0
        return
    newDeck := []
    i := b + 1
    while i <= solitaireDeck.Length {
        newDeck.Push(solitaireDeck[i])
        i += 1
    }
    i := a
    while i <= b {
        newDeck.Push(solitaireDeck[i])
        i += 1
    }
    i := 1
    while i < a {
        newDeck.Push(solitaireDeck[i])
        i += 1
    }
    solitaireDeck := newDeck
}

SolitaireCountCut(count) {
    global solitaireDeck
    if count <= 0 || count >= solitaireDeck.Length
        return
    bottom := solitaireDeck[solitaireDeck.Length]
    topPart := []
    i := 1
    while i <= count {
        topPart.Push(solitaireDeck[i])
        i += 1
    }
    middle := []
    while i < solitaireDeck.Length {
        middle.Push(solitaireDeck[i])
        i += 1
    }
    newDeck := []
    for _, v in middle
        newDeck.Push(v)
    for _, v in topPart
        newDeck.Push(v)
    newDeck.Push(bottom)
    solitaireDeck := newDeck
}



; ------------------------------------------------------------
; Additional ciphers added in v12
; ------------------------------------------------------------

Rot47Letter(letter) {
    o := Ord(letter)
    if o >= 33 && o <= 126
        return Chr(33 + Mod(o - 33 + 47, 94))
    return letter
}

CaesarCustomAlphabetLetter(letter) {
    global keyText, shiftValue
    alpha := NormalizeAlphabet(keyText)
    u := StrUpper(letter)
    idx := InStr(alpha, u) - 1
    if idx < 0
        idx := LetterIndex(u)
    mapped := SubStr(alpha, PositiveMod(idx + shiftValue, StrLen(alpha)) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

NormalizeAlphabet(text) {
    global ALPHABET
    out := ""
    for _, ch in StrSplit(CleanLetters(text)) {
        if !InStr(out, ch)
            out .= ch
    }
    for _, ch in StrSplit(ALPHABET) {
        if !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 26)
}

DellaPortaDiskLetter(letter) {
    global keyText, shiftValue
    disk := KeywordAlphabet(keyText)
    idx := LetterIndex(StrUpper(letter))
    mapped := SubStr(disk, PositiveMod(idx + shiftValue, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

LorenzToyStreamLetter(letter) {
    global keyText, streamIndex
    k := ToyWheelShift(keyText, streamIndex, [41,31,29,26,23])
    streamIndex += 1
    return ShiftLetter(letter, k)
}

HagelinToyStreamLetter(letter) {
    global keyText, streamIndex
    k := ToyWheelShift(keyText, streamIndex, [17,19,21,23,25,26])
    streamIndex += 1
    return ShiftLetter(letter, k)
}

ToyWheelShift(seed, index, wheels) {
    if seed = ""
        seed := "KEY"
    total := 0
    for i, p in wheels {
        ch := SubStr(seed, PositiveMod(index + i - 1, StrLen(seed)) + 1, 1)
        total += Mod((Ord(ch) * (i + 3)) + (index + 1) * (p + i), 26)
    }
    return Mod(total, 26)
}

RedefenceBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "Redefence")
}

RedefenceTransform(block, rails := 3, offset := 1) {
    rails := Max(2, Min(8, rails))
    rows := []
    Loop rails
        rows.Push("")
    r := PositiveMod(offset, rails) + 1
    dir := 1
    for _, ch in StrSplit(block) {
        rows[r] .= ch
        if r = rails
            dir := -1
        else if r = 1
            dir := 1
        r += dir
    }
    out := ""
    for _, row in rows
        out .= row
    return out
}

PlayfairQOmittedLetter(letter) {
    return GenericPairLetterV12(letter, "PlayfairQ")
}

DoublePlayfairLetter(letter) {
    return GenericPairLetterV12(letter, "DoublePlayfair")
}

TwinBifidLetter(letter) {
    return GenericPairLetterV12(letter, "TwinBifid")
}

GenericPairLetterV12(letter, kind) {
    global pairBuffer
    u := StrUpper(letter)
    if pairBuffer = "" {
        pairBuffer := u
        return ""
    }
    a := pairBuffer
    b := u
    pairBuffer := ""
    switch kind {
        case "PlayfairQ":
            return PlayfairQOmittedEncryptPair(a, b, IsUpperLetter(letter))
        case "DoublePlayfair":
            return DoublePlayfairEncryptPair(a, b, IsUpperLetter(letter))
        case "TwinBifid":
            return TwinBifidEncryptPair(a, b, IsUpperLetter(letter))
    }
    return a . b
}

PlayfairQOmittedEncryptPair(a, b, uppercase := true) {
    global keyText
    a := (StrUpper(a) = "Q") ? "K" : StrUpper(a)
    b := (StrUpper(b) = "Q") ? "K" : StrUpper(b)
    sq := KeywordAlphabetOmit(keyText, "Q")
    out := PlayfairPairFromSquare(a, b, sq)
    return uppercase ? out : StrLower(out)
}

KeywordAlphabetOmit(key, omit) {
    global ALPHABET
    clean := CleanLetters(key)
    out := ""
    for _, ch in StrSplit(clean) {
        if ch != omit && !InStr(out, ch)
            out .= ch
    }
    for _, ch in StrSplit(ALPHABET) {
        if ch != omit && !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 25)
}

PlayfairPairFromSquare(a, b, sq) {
    ia := InStr(sq, a) - 1
    ib := InStr(sq, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    if ra = rb {
        c1 := SubStr(sq, ra * 5 + PositiveMod(ca + 1, 5) + 1, 1)
        c2 := SubStr(sq, rb * 5 + PositiveMod(cb + 1, 5) + 1, 1)
    } else if ca = cb {
        c1 := SubStr(sq, PositiveMod(ra + 1, 5) * 5 + ca + 1, 1)
        c2 := SubStr(sq, PositiveMod(rb + 1, 5) * 5 + cb + 1, 1)
    } else {
        c1 := SubStr(sq, ra * 5 + cb + 1, 1)
        c2 := SubStr(sq, rb * 5 + ca + 1, 1)
    }
    return c1 . c2
}

DoublePlayfairEncryptPair(a, b, uppercase := true) {
    global keyText
    keys := SplitTwoKeys(keyText, "ALPHA", "OMEGA")
    sq1 := Square5(keys[1])
    sq2 := Square5(keys[2])
    first := PlayfairPairFromSquare(StrUpper(a), StrUpper(b), sq1)
    second := PlayfairPairFromSquare(SubStr(first, 1, 1), SubStr(first, 2, 1), sq2)
    return uppercase ? second : StrLower(second)
}

TwinBifidEncryptPair(a, b, uppercase := true) {
    global keyText
    keys := SplitTwoKeys(keyText, "ALPHA", "OMEGA")
    sq1 := Square5(keys[1])
    sq2 := Square5(keys[2])
    a := StrUpper(a), b := StrUpper(b)
    if a = "J"
        a := "I"
    if b = "J"
        b := "I"
    ia := InStr(sq1, a) - 1
    ib := InStr(sq2, b) - 1
    if ia < 0 || ib < 0
        return a . b
    ra := Floor(ia / 5), ca := Mod(ia, 5)
    rb := Floor(ib / 5), cb := Mod(ib, 5)
    merged := [ra, rb, ca, cb]
    c1 := SubStr(sq1, merged[1] * 5 + merged[3] + 1, 1)
    c2 := SubStr(sq2, merged[2] * 5 + merged[4] + 1, 1)
    out := c1 . c2
    return uppercase ? out : StrLower(out)
}

SplitTwoKeys(text, default1 := "ALPHA", default2 := "OMEGA") {
    parts := StrSplit(CleanLettersWithSpaces(text), " ")
    out := []
    for _, part in parts {
        if part != ""
            out.Push(part)
    }
    if out.Length < 1
        out.Push(default1)
    if out.Length < 2
        out.Push(default2)
    return out
}

PolybiusColumnarBlockLetter(letter) {
    return BlockCipherLetter(letter, 10, "PolybiusColumnar")
}

PolybiusFractionText(text, key) {
    sq := Square5(key)
    labels := "12345"
    out := ""
    for _, ch in StrSplit(StrUpper(text)) {
        u := ch = "J" ? "I" : ch
        idx := InStr(sq, u) - 1
        if idx >= 0
            out .= SubStr(labels, Floor(idx/5)+1, 1) . SubStr(labels, Mod(idx,5)+1, 1)
    }
    return out
}

Base16SeparatedLetter(letter) {
    return Format("{:02X} ", Ord(letter))
}

Base32HexPerLetter(letter) {
    b := Ord(letter)
    alpha := "0123456789ABCDEFGHIJKLMNOPQRSTUV"
    i1 := (b >> 3) + 1
    i2 := ((b & 7) << 2) + 1
    return SubStr(alpha, i1, 1) . SubStr(alpha, i2, 1) . "====== "
}

Base64UrlPerLetter(letter) {
    b := Ord(letter)
    alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
    i1 := (b >> 2) + 1
    i2 := ((b & 3) << 4) + 1
    return SubStr(alpha, i1, 1) . SubStr(alpha, i2, 1) . " "
}

Base91PerLetter(letter) {
    alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_{|}~"
    return EncodeNumberBase(Ord(letter), alpha) . " "
}

RFC1924Base85Letter(letter) {
    alpha := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_{|}~"
    return EncodeNumberBase(Ord(letter), alpha) . " "
}

YEncLetter(letter) {
    v := Mod(Ord(letter) + 42, 256)
    if v = 0 || v = 10 || v = 13 || v = 61
        return "=" . Chr(Mod(v + 64, 256)) . " "
    return Chr(v) . " "
}

EncodeNumberBase(n, alpha) {
    if n <= 0
        return SubStr(alpha, 1, 1)
    base := StrLen(alpha)
    out := ""
    while n > 0 {
        r := Mod(n, base)
        out := SubStr(alpha, r + 1, 1) . out
        n := Floor(n / base)
    }
    return out
}

PEMArmorTokenLetter(letter) {
    b64 := Base64PerLetter(letter)
    b64 := StrReplace(Trim(b64), " ", "")
    return "-----BEGIN CHAR----- " . b64 . " -----END CHAR----- "
}

MessagePackHexTokenLetter(letter) {
    return "A1" . Format("{:02X} ", Ord(letter))
}

IntelHexRecordLetter(letter) {
    b := Ord(letter)
    length := 1, addrHigh := 0, addrLow := 0, typ := 0
    sum := length + addrHigh + addrLow + typ + b
    chk := PositiveMod(-sum, 256)
    return ":" . Format("{:02X}{:02X}{:02X}{:02X}{:02X}{:02X} ", length, addrHigh, addrLow, typ, b, chk)
}

MotorolaSRecordLetter(letter) {
    b := Ord(letter)
    count := 4 ; 2 address bytes + 1 data byte + checksum
    a1 := 0, a2 := 0
    sum := count + a1 + a2 + b
    chk := 255 - Mod(sum, 256)
    return "S1" . Format("{:02X}{:02X}{:02X}{:02X}{:02X} ", count, a1, a2, b, chk)
}

CistercianNumeralLetter(letter) {
    return "[C" . Format("{:04d}", Ord(letter)) . "] "
}

MurrayCodeLetter(letter) {
    return BaudotLetter(letter)
}

APCOPhoneticLetter(letter) {
    u := StrUpper(letter)
    m := Map(
        "A","Adam ", "B","Boy ", "C","Charles ", "D","David ", "E","Edward ", "F","Frank ",
        "G","George ", "H","Henry ", "I","Ida ", "J","John ", "K","King ", "L","Lincoln ",
        "M","Mary ", "N","Nora ", "O","Ocean ", "P","Paul ", "Q","Queen ", "R","Robert ",
        "S","Sam ", "T","Tom ", "U","Union ", "V","Victor ", "W","William ", "X","X-ray ",
        "Y","Young ", "Z","Zebra "
    )
    return m.Has(u) ? m[u] : letter
}

InternationalSignalPhraseLetter(letter) {
    u := StrUpper(letter)
    m := Map(
        "A","[A diver down] ", "B","[B dangerous goods] ", "C","[C yes] ", "D","[D keep clear] ",
        "E","[E altering starboard] ", "F","[F disabled] ", "G","[G require pilot] ", "H","[H pilot aboard] ",
        "I","[I altering port] ", "J","[J on fire] ", "K","[K communicate] ", "L","[L stop instantly] ",
        "M","[M stopped] ", "N","[N no] ", "O","[O man overboard] ", "P","[P about to proceed] ",
        "Q","[Q request pratique] ", "R","[R received] ", "S","[S astern propulsion] ", "T","[T keep clear] ",
        "U","[U danger] ", "V","[V assistance] ", "W","[W medical assistance] ", "X","[X stop intentions] ",
        "Y","[Y dragging anchor] ", "Z","[Z require tug] "
    )
    return m.Has(u) ? m[u] : letter
}

YoungerFutharkLetter(letter) {
    chars := StrSplit("ᛅ|ᛒ|ᚴ|ᛏ|ᛁ|ᚠ|ᚴ|ᚼ|ᛁ|ᛁ|ᚴ|ᛚ|ᛘ|ᚾ|ᚢ|ᛒ|ᚴ|ᚱ|ᛋ|ᛏ|ᚢ|ᚠ|ᚢ|ᚴᛋ|ᛦ|ᛋ", "|")
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

CirthRuneLetter(letter) {
    u := StrUpper(letter)
    s := "ᚠᚢᚦᚨᚱᚲᚷᚹᚺᛁᛃᛇᛈᛉᛊᛏᛒᛖᛗᛚᛜᛟᛞᚪᚫᚣ"
    idx := LetterIndex(u)
    return idx >= 0 ? SubStr(s, idx + 1, 1) : letter
}

TengwarTokenLetter(letter) {
    u := StrUpper(letter)
    tokens := ["tinco","parma","calma","quesse","ando","umbar","anga","ungwe","thule","formen","harma","hwesta","anto","ampa","anca","unque","numen","malta","noldo","nwalme","ore","vala","anna","vilya","romen","arda"]
    idx := LetterIndex(u)
    return idx >= 0 ? "[" . tokens[idx + 1] . "] " : letter
}

ZodiacSymbolLetter(letter) {
    u := StrUpper(letter)
    s := "♈♉♊♋♌♍♎♏♐♑♒♓☉☽☿♀♂♃♄⛢♆♇⚷⚸⚹⚺"
    idx := LetterIndex(u)
    return idx >= 0 ? SubStr(s, idx + 1, 1) : letter
}

WingdingsTokenLetter(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    return "[wd-" . Format("{:02d}", idx) . "] "
}

BrailleGrade1Letter(letter) {
    return BrailleLetter(letter)
}

BaconBiliteralCustomLetter(letter) {
    global keyText
    a := SubStr(keyText, 1, 1)
    b := SubStr(keyText, 2, 1)
    if a = ""
        a := "A"
    if b = ""
        b := "B"
    bits := Binary5Letter(letter)
    bits := RegExReplace(bits, "[^01]", "")
    out := ""
    for _, ch in StrSplit(bits)
        out .= ch = "1" ? b : a
    return out . " "
}

SolresolLetter(letter) {
    sol := ["do","re","mi","fa","sol","la","si"]
    idx := LetterIndex(StrUpper(letter))
    return sol[Floor(idx / 7) + 1] . "-" . sol[Mod(idx, 7) + 1] . " "
}

MusicNoteLetter(letter) {
    notes := ["C","D","E","F","G","A","B"]
    idx := LetterIndex(StrUpper(letter))
    return notes[Mod(idx, 7) + 1] . (4 + Floor(idx / 7)) . " "
}

NullAcrosticWordLetter(letter) {
    words := StrSplit("able |baker |charlie |delta |eager |foxtrot |golf |hotel |item |jolly |kilo |lima |mike |november |orange |papa |queen |romeo |sierra |tango |union |victor |whiskey |xray |yankee |zebra ", "|")
    return words[LetterIndex(StrUpper(letter)) + 1]
}

AcrosticCoverWordLetter(letter) {
    global keyText
    tail := StrLower(CleanLetters(keyText))
    if tail = ""
        tail := "cover"
    tail := SubStr(tail, 2)
    if tail = ""
        tail := "word"
    return StrUpper(letter) . tail . " "
}

CalculatorSpellingLetter(letter) {
    u := StrUpper(letter)
    m := Map("O","0", "I","1", "Z","2", "E","3", "H","4", "S","5", "G","6", "L","7", "B","8", "Q","9")
    return m.Has(u) ? m[u] : letter
}

VanityPhoneDigitLetter(letter) {
    return PhoneT9DigitLetter(letter)
}

KeyboardCoordinateLetter(letter) {
    u := StrUpper(letter)
    rows := ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
    for r, row in rows {
        c := InStr(row, u)
        if c > 0
            return r . "." . c . " "
    }
    return letter
}

QwertyAdjacentUpLetter(letter) {
    return QwertyAdjacentVertical(letter, -1)
}

QwertyAdjacentDownLetter(letter) {
    return QwertyAdjacentVertical(letter, 1)
}

QwertyAdjacentVertical(letter, delta) {
    u := StrUpper(letter)
    rows := ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
    for r, row in rows {
        c := InStr(row, u)
        if c > 0 {
            nr := PositiveMod(r - 1 + delta, rows.Length) + 1
            nrow := rows[nr]
            nc := Min(c, StrLen(nrow))
            out := SubStr(nrow, nc, 1)
            return IsUpperLetter(letter) ? out : StrLower(out)
        }
    }
    return letter
}

ChessboardCoordinateLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    files := "ABCDEFGH"
    squareIndex := idx
    file := SubStr(files, Mod(squareIndex, 8) + 1, 1)
    rank := Floor(squareIndex / 8) + 1
    return file . rank . " "
}

; ------------------------------------------------------------
; Utilities
; ------------------------------------------------------------

IndexOf(arr, value) {
    for i, v in arr {
        if v = value
            return i
    }
    return 1
}

SelectedFrom(ctrl, arr) {
    idx := ctrl.Value
    if idx < 1 || idx > arr.Length
        return arr[1]
    return arr[idx]
}

ToIntegerOrDefault(value, defaultValue) {
    value := Trim(value)
    if RegExMatch(value, "^-?\d+$")
        return value + 0
    return defaultValue
}

PositiveMod(n, m) {
    return Mod(Mod(n, m) + m, m)
}

CleanLetters(text) {
    return RegExReplace(StrUpper(text), "[^A-Z]", "")
}

CleanDigits(text) {
    return RegExReplace(text, "[^0-9]", "")
}

DigitShiftAt(key, index) {
    clean := CleanDigits(key)
    if clean = ""
        clean := "0"
    pos := PositiveMod(index, StrLen(clean)) + 1
    return SubStr(clean, pos, 1) + 0
}

NormalizeLettersToLength(text, length, padChar := "A") {
    clean := CleanLetters(text)
    while StrLen(clean) < length
        clean .= padChar
    return SubStr(clean, 1, length)
}

IsUpperLetter(letter) {
    return letter ~= "^[A-Z]$"
}

LetterIndex(letter) {
    global ALPHABET
    return InStr(ALPHABET, StrUpper(letter)) - 1
}

LetterFromIndex(index, uppercase := true) {
    global ALPHABET
    letter := SubStr(ALPHABET, PositiveMod(index, 26) + 1, 1)
    return uppercase ? letter : StrLower(letter)
}

KeyShiftAt(key, index) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "A"
    pos := PositiveMod(index, StrLen(clean)) + 1
    ch := SubStr(clean, pos, 1)
    return LetterIndex(ch)
}

AutoKeyShiftAt(key, index, history) {
    clean := CleanLetters(key)
    if clean = ""
        clean := "A"
    if index < StrLen(clean) {
        ch := SubStr(clean, index + 1, 1)
        return LetterIndex(ch)
    }
    hpos := index - StrLen(clean) + 1
    if hpos >= 1 && hpos <= StrLen(history)
        return LetterIndex(SubStr(history, hpos, 1))
    return 0
}

IsValidAffineA(a) {
    valid := [1,3,5,7,9,11,15,17,19,21,23,25]
    for _, v in valid {
        if a = v
            return true
    }
    return false
}

NormalizeSubstitutionAlphabet(text) {
    global ALPHABET
    clean := CleanLetters(text)
    out := ""
    for _, ch in StrSplit(clean) {
        if !InStr(out, ch)
            out .= ch
    }
    for _, ch in StrSplit(ALPHABET) {
        if !InStr(out, ch)
            out .= ch
    }
    return SubStr(out, 1, 26)
}


RandomSubstitutionAlphabet() {
    return RandomAlphabet()
}

RandomKey(length := 8) {
    return RandomLetters(length)
}

RepeatChar(ch, count) {
    count := Integer(count)
    if count <= 0
        return ""
    out := ""
    Loop count
        out .= ch
    return out
}

Square5(key := "KEYWORD") {
    return PlayfairSquare(key)
}

RandomAlphabet() {
    global ALPHABET
    arr := StrSplit(ALPHABET)
    i := arr.Length
    while i > 1 {
        j := Random(1, i)
        tmp := arr[i]
        arr[i] := arr[j]
        arr[j] := tmp
        i -= 1
    }
    out := ""
    for _, ch in arr
        out .= ch
    return out
}


; ------------------------------------------------------------
; v17 additional ciphers / encodings
; ------------------------------------------------------------

KeyedCaesarLetter(letter) {
    global keyText, shiftValue
    alpha := KeywordAlphabet(keyText)
    u := StrUpper(letter)
    idx := InStr(alpha, u) - 1
    if idx < 0
        return letter
    out := SubStr(alpha, PositiveMod(idx + shiftValue, 26) + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

KeyedProgressiveCaesarLetter(letter) {
    global keyText, shiftValue, streamIndex
    alpha := KeywordAlphabet(keyText)
    u := StrUpper(letter)
    idx := InStr(alpha, u) - 1
    if idx < 0
        return letter
    out := SubStr(alpha, PositiveMod(idx + shiftValue + streamIndex, 26) + 1, 1)
    streamIndex += 1
    return IsUpperLetter(letter) ? out : StrLower(out)
}

InterruptedKeyVigenereLetter(letter) {
    global keyText, shiftValue, streamIndex
    key := CleanLetters(keyText)
    if key = ""
        key := "A"
    period := Max(1, Integer(shiftValue))
    kpos := Mod(streamIndex, period)
    shift := LetterIndex(SubStr(key, Mod(kpos, StrLen(key)) + 1, 1))
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

ProgressiveKeyVigenereLetter(letter) {
    global keyText, shiftValue, streamIndex
    baseShift := KeyShiftAt(keyText, streamIndex)
    groupShift := Floor(streamIndex / 5) * Integer(shiftValue)
    streamIndex += 1
    return ShiftLetter(letter, baseShift + groupShift)
}

VariantBeaufortAutokeyLetter(letter) {
    global keyText, autoKeyHistory, streamIndex
    shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
    streamIndex += 1
    autoKeyHistory .= StrUpper(letter)
    return ShiftLetter(letter, -shift)
}

RunningKeyBookLetter(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

ProgressiveBeaufortLetter(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex) + streamIndex
    streamIndex += 1
    return LetterFromIndex(PositiveMod(shift - LetterIndex(StrUpper(letter)), 26), IsUpperLetter(letter))
}

ProgressiveVariantBeaufortLetter(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex) + streamIndex
    streamIndex += 1
    return ShiftLetter(letter, -shift)
}

PortaAutokeyLetter(letter) {
    global keyText, autoKeyHistory, streamIndex
    key := CleanLetters(keyText) . autoKeyHistory
    if key = ""
        key := "A"
    kidx := Floor(LetterIndex(SubStr(key, Mod(streamIndex, StrLen(key)) + 1, 1)) / 2)
    x := LetterIndex(StrUpper(letter))
    if x < 13
        y := PositiveMod(x + 13 - kidx, 13) + 13
    else
        y := PositiveMod(x - 13 + kidx, 13)
    streamIndex += 1
    autoKeyHistory .= StrUpper(letter)
    return LetterFromIndex(y, IsUpperLetter(letter))
}

TriangularCaesarShiftLetter(letter) {
    global streamIndex
    n := streamIndex + 1
    streamIndex += 1
    return ShiftLetter(letter, Floor(n * (n + 1) / 2))
}

LucasNumber(n) {
    if n <= 1
        return 2
    if n = 2
        return 1
    a := 2, b := 1
    Loop n - 2 {
        c := a + b
        a := b
        b := c
    }
    return b
}

LucasCaesarShiftLetter(letter) {
    global streamIndex
    n := streamIndex + 1
    streamIndex += 1
    return ShiftLetter(letter, LucasNumber(n))
}

SquareCaesarShiftLetter(letter) {
    global streamIndex
    n := streamIndex + 1
    streamIndex += 1
    return ShiftLetter(letter, n * n)
}

CubeCaesarShiftLetter(letter) {
    global streamIndex
    n := streamIndex + 1
    streamIndex += 1
    return ShiftLetter(letter, n * n * n)
}

DigitalRootCaesarShiftLetter(letter) {
    global streamIndex
    n := streamIndex + 1
    streamIndex += 1
    root := 1 + Mod(n - 1, 9)
    return ShiftLetter(letter, root)
}

AlternatingAtbashLetter(letter) {
    global streamIndex
    out := Mod(streamIndex, 2) = 0 ? AtbashLetter(letter) : ShiftLetter(letter, 13)
    streamIndex += 1
    return out
}

VigenereAtbashHybridLetter(letter) {
    global keyText, streamIndex
    at := AtbashLetter(letter)
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return ShiftLetter(at, shift)
}

Polybius0BasedKeyedLetter(letter) {
    global keyText
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    sq := Square5(keyText)
    idx := InStr(sq, u) - 1
    if idx < 0
        return letter
    return Floor(idx / 5) . Mod(idx, 5) . " "
}

PolybiusLetterCoordsKeyedLetter(letter) {
    global keyText
    labels := "ABCDE"
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    sq := Square5(keyText)
    idx := InStr(sq, u) - 1
    if idx < 0
        return letter
    return SubStr(labels, Floor(idx / 5) + 1, 1) . SubStr(labels, Mod(idx, 5) + 1, 1) . " "
}

GrandpreGrid(key) {
    clean := CleanLetters(key)
    source := clean . "ABCDEFGHIJKLMNOPQRSTUVWXYZABCDEFGHIJKLMNOPQRSTUVWXYZABCDEFGHIJKLMNOPQRSTUVWXYZ"
    return SubStr(source, 1, 100)
}

GrandpreCoordinateLetter(letter) {
    global keyText, streamIndex
    grid := GrandpreGrid(keyText)
    u := StrUpper(letter)
    start := Mod(streamIndex * 7, 100) + 1
    found := 0
    Loop 100 {
        pos := Mod(start + A_Index - 2, 100) + 1
        if SubStr(grid, pos, 1) = u {
            found := pos
            break
        }
    }
    streamIndex += 1
    if found = 0
        return letter
    found -= 1
    return Floor(found / 10) . Mod(found, 10) . " "
}

FractionatedPolybiusTokenLetter(letter) {
    global keyText
    u := StrUpper(letter)
    if u = "J"
        u := "I"
    sq := Square5(keyText)
    idx := InStr(sq, u) - 1
    if idx < 0
        return letter
    rows := ["A","D","F","G","X"]
    return rows[Floor(idx / 5) + 1] . "." . rows[Mod(idx, 5) + 1] . " "
}

Base26A0Z25Letter(letter) {
    return BaseN(LetterIndex(StrUpper(letter)), 26) . " "
}

AsciiHexLowerLetter(letter) {
    return StrLower(Format("{:02X}", Ord(letter))) . " "
}

AsciiDecimalPaddedLetter(letter) {
    return Format("{:03d}", Ord(letter)) . " "
}

BinaryAscii7Letter(letter) {
    return ToBinaryWidth(Ord(letter) & 0x7F, 7) . " "
}

UnicodeDecimalCodePointLetter(letter) {
    return Ord(letter) . " "
}

Utf16BEHexLetter(letter) {
    code := Ord(letter)
    return Format("{:02X} {:02X} ", (code >> 8) & 0xFF, code & 0xFF)
}

Utf32BEHexLetter(letter) {
    code := Ord(letter)
    return Format("{:02X} {:02X} {:02X} {:02X} ", (code >> 24) & 0xFF, (code >> 16) & 0xFF, (code >> 8) & 0xFF, code & 0xFF)
}

Utf32LEHexLetter(letter) {
    code := Ord(letter)
    return Format("{:02X} {:02X} {:02X} {:02X} ", code & 0xFF, (code >> 8) & 0xFF, (code >> 16) & 0xFF, (code >> 24) & 0xFF)
}

XmlDecimalEntityLetter(letter) {
    return "&#" . Ord(letter) . ";"
}

XmlHexEntityLetter(letter) {
    return "&#x" . Format("{:X}", Ord(letter)) . ";"
}

LatinAlphabetNameLetter(letter) {
    names := ["Alpha","Bravo","Charlie","Delta","Echo","Foxtrot","Golf","Hotel","India","Juliet","Kilo","Lima","Mike","November","Oscar","Papa","Quebec","Romeo","Sierra","Tango","Uniform","Victor","Whiskey","Xray","Yankee","Zulu"]
    return names[LetterIndex(StrUpper(letter)) + 1] . " "
}

GreekAlphabetNameLetter(letter) {
    names := ["Alpha","Beta","Gamma","Delta","Epsilon","Zeta","Eta","Theta","Iota","Kappa","Lambda","Mu","Nu","Xi","Omicron","Pi","Rho","Sigma","Tau","Upsilon","Phi","Chi","Psi","Omega","Stigma","Sampi"]
    return names[LetterIndex(StrUpper(letter)) + 1] . " "
}

HebrewGematriaLetter(letter) {
    vals := [1,2,3,4,5,6,7,8,9,10,20,30,40,50,60,70,80,90,100,200,300,400,500,600,700,800]
    return vals[LetterIndex(StrUpper(letter)) + 1] . " "
}

GreekIsopsephyLetter(letter) {
    vals := [1,2,3,4,5,7,8,9,10,20,30,40,50,60,70,80,100,200,300,400,500,600,700,800,900,1000]
    return vals[LetterIndex(StrUpper(letter)) + 1] . " "
}

ScrabbleValueLetter(letter) {
    vals := StrSplit("1|3|3|2|1|4|2|4|1|8|5|1|3|1|1|3|10|1|1|1|1|4|4|8|4|10", "|")
    return vals[LetterIndex(StrUpper(letter)) + 1] . " "
}

LetterFrequencyRankLetter(letter) {
    order := "ETAOINSHRDLCUMWFGYPBVKJXQZ"
    return InStr(order, StrUpper(letter)) . " "
}

PeriodicAtomicNumberLetter(letter) {
    return (LetterIndex(StrUpper(letter)) + 1) . " "
}

PeriodicElementSymbolLetter(letter) {
    syms := ["H","He","Li","Be","B","C","N","O","F","Ne","Na","Mg","Al","Si","P","S","Cl","Ar","K","Ca","Sc","Ti","V","Cr","Mn","Fe"]
    return syms[LetterIndex(StrUpper(letter)) + 1] . " "
}

NatoCompactLetter(letter) {
    return StrUpper(letter) . "-" . NatoLetter(letter)
}

LapdPhoneticLetter(letter) {
    words := ["Adam","Boy","Charles","David","Edward","Frank","George","Henry","Ida","John","King","Lincoln","Mary","Nora","Ocean","Paul","Queen","Robert","Sam","Tom","Union","Victor","William","Xray","Young","Zebra"]
    return words[LetterIndex(StrUpper(letter)) + 1] . " "
}

RafPhoneticLetter(letter) {
    words := ["Able","Baker","Charlie","Dog","Easy","Fox","George","How","Item","Jig","King","Love","Mike","Nan","Oboe","Peter","Queen","Roger","Sugar","Tare","Uncle","Victor","William","Xray","Yoke","Zebra"]
    return words[LetterIndex(StrUpper(letter)) + 1] . " "
}

MorseRaw(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    codes := StrSplit(".-|-...|-.-.|-..|.|..-.|--.|....|..|.---|-.-|.-..|--|-.|---|.--.|--.-|.-.|...|-|..-|...-|.--|-..-|-.--|--..", "|")
    return (idx >= 1 && idx <= codes.Length) ? codes[idx] : ""
}

MorseLengthCodeLetter(letter) {
    return StrLen(MorseRaw(letter)) . " "
}

MorseDashCountLetter(letter) {
    code := MorseRaw(letter)
    return StrLen(StrReplace(code, ".", "")) . " "
}

MorseDotCountLetter(letter) {
    code := MorseRaw(letter)
    return StrLen(StrReplace(code, "-", "")) . " "
}

FlagTokenLetter(letter) {
    return "[FLAG-" . StrUpper(letter) . "] "
}

MoonTypeTokenLetter(letter) {
    return "[MOON-" . Format("{:02d}", LetterIndex(StrUpper(letter)) + 1) . "] "
}

ThebanTokenLetter(letter) {
    return "[THEBAN-" . Format("{:02d}", LetterIndex(StrUpper(letter)) + 1) . "] "
}

DancingMenTokenLetter(letter) {
    return "[DANCING-" . StrUpper(letter) . "] "
}

StandardGalacticTokenLetter(letter) {
    return "[SGA-" . StrUpper(letter) . "] "
}

AurebeshTokenLetter(letter) {
    return "[AUREBESH-" . StrUpper(letter) . "] "
}

MathPlaneUpper(letter, base) {
    return Chr(base + LetterIndex(StrUpper(letter)))
}

MathBoldLetter(letter) {
    return MathPlaneUpper(letter, 0x1D400)
}

MathItalicLetter(letter) {
    return MathPlaneUpper(letter, 0x1D434)
}

SansSerifLetter(letter) {
    return MathPlaneUpper(letter, 0x1D5A0)
}

SansSerifBoldLetter(letter) {
    return MathPlaneUpper(letter, 0x1D5D4)
}

MonospaceLetter(letter) {
    return MathPlaneUpper(letter, 0x1D670)
}

NegativeCircledLetter(letter) {
    return Chr(0x1F150 + LetterIndex(StrUpper(letter))) . " "
}

BoxDrawingCodeLetter(letter) {
    chars := ["─","━","│","┃","┄","┅","┆","┇","┈","┉","┊","┋","┌","┍","┎","┏","┐","┑","┒","┓","└","┕","┖","┗","┘","┙"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

GeometricShapeLetter(letter) {
    chars := ["○","●","◐","◑","◒","◓","◔","◕","◖","◗","◌","◍","◎","◉","□","■","▢","▣","▤","▥","▦","▧","▨","▩","△","▲"]
    return chars[LetterIndex(StrUpper(letter)) + 1] . " "
}


; ------------------------------------------------------------
; v18 additional ciphers / encodings
; ------------------------------------------------------------

VigenereKeyedAlphabetLetter(letter) {
    global keyText, streamIndex
    alpha := KeywordAlphabet(keyText)
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    y := PositiveMod(LetterIndex(StrUpper(letter)) + shift, 26)
    out := SubStr(alpha, y + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

BeaufortKeyedAlphabetLetter(letter) {
    global keyText, streamIndex
    alpha := KeywordAlphabet(keyText)
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    y := PositiveMod(shift - LetterIndex(StrUpper(letter)), 26)
    out := SubStr(alpha, y + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

VariantBeaufortKeyedAlphabetLetter(letter) {
    global keyText, streamIndex
    alpha := KeywordAlphabet(keyText)
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    y := PositiveMod(LetterIndex(StrUpper(letter)) - shift, 26)
    out := SubStr(alpha, y + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

AutokeyKeyedAlphabetLetter(letter) {
    global keyText, streamIndex, autoKeyHistory
    alpha := KeywordAlphabet(keyText)
    shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
    streamIndex += 1
    autoKeyHistory .= StrUpper(letter)
    y := PositiveMod(LetterIndex(StrUpper(letter)) + shift, 26)
    out := SubStr(alpha, y + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

PortaNumericTableLetter(letter) {
    global keyText, streamIndex
    kidx := Floor(KeyShiftAt(keyText, streamIndex) / 2)
    streamIndex += 1
    x := LetterIndex(StrUpper(letter))
    if x < 13
        y := PositiveMod(x + kidx, 13) + 13
    else
        y := PositiveMod(x - 13 - kidx, 13)
    return Format("{:02d} ", y + 1)
}

PortaReverseTableLetter(letter) {
    global keyText, streamIndex
    kidx := Floor(KeyShiftAt(keyText, streamIndex) / 2)
    streamIndex += 1
    x := LetterIndex(StrUpper(letter))
    if x < 13
        y := PositiveMod(12 - x + kidx, 13) + 13
    else
        y := PositiveMod(12 - (x - 13) - kidx, 13)
    return LetterFromIndex(y, IsUpperLetter(letter))
}

AtbashThenVigenereLetter(letter) {
    global keyText, streamIndex
    a := 25 - LetterIndex(StrUpper(letter))
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return LetterFromIndex(a + shift, IsUpperLetter(letter))
}

VigenereThenAtbashLetter(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    v := PositiveMod(LetterIndex(StrUpper(letter)) + shift, 26)
    return LetterFromIndex(25 - v, IsUpperLetter(letter))
}

RunningAtbashKeyLetter(letter) {
    global keyText, streamIndex
    shift := 25 - KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

AutokeyAtbashLetter(letter) {
    global keyText, streamIndex, autoKeyHistory
    shift := 25 - AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
    streamIndex += 1
    autoKeyHistory .= StrUpper(letter)
    return ShiftLetter(letter, shift)
}

ProgressiveAffineLetter(letter) {
    global streamIndex
    x := LetterIndex(StrUpper(letter))
    y := PositiveMod((5 * x) + 8 + streamIndex, 26)
    streamIndex += 1
    return LetterFromIndex(y, IsUpperLetter(letter))
}

ProgressiveDecimationLetter(letter) {
    global streamIndex
    factors := [3,5,7,11,17,25]
    a := factors[Mod(streamIndex, factors.Length) + 1]
    x := LetterIndex(StrUpper(letter))
    y := PositiveMod(a * x + streamIndex, 26)
    streamIndex += 1
    return LetterFromIndex(y, IsUpperLetter(letter))
}

MultiplicativeFixedLetter(letter, factor) {
    x := LetterIndex(StrUpper(letter))
    return LetterFromIndex(Integer(factor) * x, IsUpperLetter(letter))
}

BaconBits(letter) {
    return ToBinaryWidth(LetterIndex(StrUpper(letter)), 5)
}

BaconianBinaryLetter(letter) {
    return BaconBits(letter) . " "
}

BaconianReversedLetter(letter) {
    return ReverseString(BaconBits(letter)) . " "
}

BaconianDotsDashesLetter(letter) {
    bits := BaconBits(letter)
    return StrReplace(StrReplace(bits, "0", "."), "1", "-") . " "
}

BaconianVisibleWhitespaceLetter(letter) {
    bits := BaconBits(letter)
    return StrReplace(StrReplace(bits, "0", "S"), "1", "T") . " "
}

MorseBitsFromRaw(letter, dotBit, dashBit) {
    code := MorseRaw(letter)
    return StrReplace(StrReplace(code, ".", dotBit), "-", dashBit)
}

MorseBinary10Letter(letter) {
    return MorseBitsFromRaw(letter, "1", "0") . " "
}

MorseBinary01Letter(letter) {
    return MorseBitsFromRaw(letter, "0", "1") . " "
}

MorseWithSlashLetter(letter) {
    return MorseRaw(letter) . "/"
}

MorseCompactDigitsLetter(letter) {
    return MorseBitsFromRaw(letter, "1", "2") . " "
}

MorseDecimalTokenLetter(letter) {
    bits := MorseBitsFromRaw(letter, "0", "1")
    val := BinaryStringToInteger(bits)
    return val . " "
}

MorseHexTokenLetter(letter) {
    bits := MorseBitsFromRaw(letter, "0", "1")
    val := BinaryStringToInteger(bits)
    return Format("{:X} ", val)
}

BinaryStringToInteger(bits) {
    n := 0
    Loop Parse, bits
        n := (n * 2) + Integer(A_LoopField)
    return n
}

Polybius6x6Letter(letter) {
    alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    idx := InStr(alpha, StrUpper(letter)) - 1
    r := Floor(idx / 6) + 1
    c := Mod(idx, 6) + 1
    return r . c . " "
}

ADFGVX6x6CoordLetter(letter) {
    labels := "ADFGVX"
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / 6) + 1
    c := Mod(idx, 6) + 1
    return SubStr(labels, r, 1) . SubStr(labels, c, 1) . " "
}

BifidNumericFractionLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / 5) + 1
    c := Mod(idx, 5) + 1
    return r . "|" . c . " "
}

TrifidNumericFractionLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    layer := Floor(idx / 9) + 1
    rest := Mod(idx, 9)
    row := Floor(rest / 3) + 1
    col := Mod(rest, 3) + 1
    return layer . row . col . " "
}

NihilistPlainCoordinateLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / 5) + 1
    c := Mod(idx, 5) + 1
    return ((r * 10) + c) . " "
}

Checkerboard6x6CoordLetter(letter) {
    idx := LetterIndex(StrUpper(letter))
    return Floor(idx / 6) . "." . Mod(idx, 6) . " "
}

BaseIndexLetter(letter, base) {
    n := LetterIndex(StrUpper(letter)) + 1
    return BaseN(n, Integer(base)) . " "
}

QRAlphanumericIndexLetter(letter) {
    qr := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
    return (InStr(qr, StrUpper(letter)) - 1) . " "
}

Code39TokenLetter(letter) {
    return "*" . StrUpper(letter) . "* "
}

CodabarTokenLetter(letter) {
    return "A" . Format("{:02d}", LetterIndex(StrUpper(letter)) + 10) . "B "
}

Code128TokenLetter(letter) {
    return "[C128:" . Ord(StrUpper(letter)) . "] "
}

ITFTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return Format("{:02d}", n) . " "
}

UPCACheckTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    body := "04210000" . Format("{:03d}", n)
    return body . Mod10CheckDigit(body, false) . " "
}

EAN13CheckTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    body := "978000000" . Format("{:03d}", n)
    return body . Mod10CheckDigit(body, true) . " "
}

ISBN10CheckTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    body := "000000" . Format("{:03d}", n)
    sum := 0
    Loop Parse, body
        sum += Integer(A_LoopField) * A_Index
    check := Mod(sum, 11)
    return body . (check = 10 ? "X" : check) . " "
}

ISBN13CheckTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    body := "978000000" . Format("{:03d}", n)
    return body . Mod10CheckDigit(body, true) . " "
}

Mod10CheckDigit(body, evenThree := true) {
    sum := 0
    Loop Parse, body {
        d := Integer(A_LoopField)
        if evenThree
            weight := (Mod(A_Index, 2) = 0) ? 3 : 1
        else
            weight := (Mod(A_Index, 2) = 1) ? 3 : 1
        sum += d * weight
    }
    return Mod(10 - Mod(sum, 10), 10)
}

MathDoubleStruckLetter(letter) {
    return MathPlaneUpper(letter, 0x1D538)
}

MathBoldItalicLetter(letter) {
    return MathPlaneUpper(letter, 0x1D468)
}

MathBoldScriptLetter(letter) {
    return MathPlaneUpper(letter, 0x1D4D0)
}

MathBoldFrakturLetter(letter) {
    return MathPlaneUpper(letter, 0x1D56C)
}

SansSerifItalicLetter(letter) {
    return MathPlaneUpper(letter, 0x1D608)
}

SansSerifBoldItalicLetter(letter) {
    return MathPlaneUpper(letter, 0x1D63C)
}

GreekActualLetter(letter) {
    chars := ["Α","Β","Γ","Δ","Ε","Ζ","Η","Θ","Ι","Κ","Λ","Μ","Ν","Ξ","Ο","Π","Ρ","Σ","Τ","Υ","Φ","Χ","Ψ","Ω","Ϟ","Ϡ"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

HebrewActualLetter(letter) {
    chars := ["א","ב","ג","ד","ה","ו","ז","ח","ט","י","כ","ל","מ","נ","ס","ע","פ","צ","ק","ר","ש","ת","ך","ם","ן","ף"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

CyrillicActualLetter(letter) {
    chars := ["А","Б","В","Г","Д","Е","Ж","З","И","Й","К","Л","М","Н","О","П","Р","С","Т","У","Ф","Х","Ц","Ч","Ш","Щ"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

ArmenianActualLetter(letter) {
    chars := ["Ա","Բ","Գ","Դ","Ե","Զ","Է","Ը","Թ","Ժ","Ի","Լ","Խ","Ծ","Կ","Հ","Ձ","Ղ","Ճ","Մ","Յ","Ն","Շ","Ո","Չ","Պ"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

GeorgianActualLetter(letter) {
    chars := ["ა","ბ","გ","დ","ე","ვ","ზ","თ","ი","კ","ლ","მ","ნ","ო","პ","ჟ","რ","ს","ტ","უ","ფ","ქ","ღ","ყ","შ","ჩ"]
    return chars[LetterIndex(StrUpper(letter)) + 1]
}

KatakanaPhoneticLetter(letter) {
    chars := ["ア","ブ","ク","ド","エ","フ","グ","ホ","イ","ジ","カ","ル","ム","ン","オ","プ","ク","ラ","ス","ト","ウ","ヴ","ワ","クス","ヤ","ズ"]
    return chars[LetterIndex(StrUpper(letter)) + 1] . " "
}


; ------------------------------------------------------------
; v19 additional live ciphers / encodings
; ------------------------------------------------------------

LatinReverseCustomLetter(letter) {
    return AtbashLetter(letter)
}

HeadlinePuzzleWordsLetter(letter) {
    words := StrSplit("Able|Baker|Charlie|Delta|Eagle|Falcon|Garden|Harbor|Ivory|Jupiter|Kingdom|Lantern|Mountain|November|Ocean|Palace|Quartz|River|Signal|Tower|Union|Victor|Winter|Xray|Yankee|Zephyr", "|")
    return words[LetterIndex(StrUpper(letter)) + 1] . " "
}

DictionaryCodeIndexLetter(letter) {
    u := StrUpper(letter)
    dictionary := ["able","baker","charlie","delta","eagle","falcon","garden","harbor","ivory","jupiter","kingdom","lantern","mountain","november","ocean","palace","quartz","river","signal","tower","union","victor","winter","xray","yankee","zephyr"]
    idx := LetterIndex(u) + 1
    return idx . ".1:" . dictionary[idx] . " "
}

RasterBitsTokenLetter(letter) {
    bits := ToBinaryWidth(Ord(letter), 8)
    return StrReplace(StrReplace(bits, "1", "#"), "0", ".") . " "
}

WhitespaceBinaryTokenLetter(letter) {
    bits := ToBinaryWidth(Ord(letter), 8)
    return StrReplace(StrReplace(bits, "1", "T"), "0", "S") . " "
}

SnowStegoSpacesTokenLetter(letter) {
    bits := ToBinaryWidth(Ord(letter), 8)
    return "[SNOW:" . StrReplace(StrReplace(bits, "1", "__"), "0", "_") . "] "
}

OpenPGPArmorTokenLetter(letter) {
    return "-----BEGIN PGP CHAR-----" . Format("{:02X}", Ord(letter)) . "-----END PGP CHAR----- "
}

Base100EmojiByteLetter(letter) {
    b := Ord(letter)
    return Chr(0x1F300 + Mod(b, 80)) . Chr(0x1F300 + Floor(b / 80)) . " "
}

HexdumpByteLetter(letter) {
    b := Ord(letter)
    return Format("00000000  {:02X}  |{}| ", b, letter)
}

BinaryEndianWordLetter(letter) {
    b := Ord(letter)
    return ToBinaryWidth(b, 8) . ":" . ToBinaryWidth(((b & 0x0F) << 4) | ((b & 0xF0) >> 4), 8) . " "
}

ChecksumToken(letter, seed := 0, mul := 131, modv := 65536, width := 4) {
    v := Mod((seed + Ord(letter)) * mul + LetterIndex(StrUpper(letter)) + 1, modv)
    return Format("{:0" . width . "X}", v) . " "
}

CRC64TokenLetter(letter) {
    return ChecksumToken(letter, 0xC96C, 1099511628211, 0x100000000, 8)
}

Fletcher32TokenLetter(letter) {
    b := Ord(letter)
    s1 := Mod(b + 1, 65535)
    s2 := Mod(s1 + b + 26, 65535)
    return Format("{:04X}{:04X} ", s2, s1)
}

VerhoeffDigit(num) {
    static d := [[0,1,2,3,4,5,6,7,8,9],[1,2,3,4,0,6,7,8,9,5],[2,3,4,0,1,7,8,9,5,6],[3,4,0,1,2,8,9,5,6,7],[4,0,1,2,3,9,5,6,7,8],[5,9,8,7,6,0,4,3,2,1],[6,5,9,8,7,1,0,4,3,2],[7,6,5,9,8,2,1,0,4,3],[8,7,6,5,9,3,2,1,0,4],[9,8,7,6,5,4,3,2,1,0]]
    static p := [[0,1,2,3,4,5,6,7,8,9],[1,5,7,6,2,8,3,0,9,4],[5,8,0,3,7,9,6,1,4,2],[8,9,1,6,0,4,3,5,2,7],[9,4,5,3,1,2,6,8,7,0],[4,2,8,6,5,7,3,9,0,1],[2,7,9,3,8,0,6,4,1,5],[7,0,4,6,9,1,3,2,5,8]]
    static inv := [0,4,3,2,1,5,6,7,8,9]
    c := 0
    rev := ReverseString((num . ""))
    Loop Parse, rev {
        digit := Integer(A_LoopField)
        c := d[c + 1][p[Mod(A_Index, 8) + 1][digit + 1] + 1]
    }
    return inv[c + 1]
}

VerhoeffCheckTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return n . VerhoeffDigit(n) . " "
}

MD5ToyTokenLetter(letter) {
    return "md5:" . ChecksumToken(letter, 0x6745, 127, 0x1000000, 6)
}

SHA1ToyTokenLetter(letter) {
    return "sha1:" . ChecksumToken(letter, 0xEFCD, 257, 0x1000000, 6)
}

SHA256ToyTokenLetter(letter) {
    return "sha256:" . ChecksumToken(letter, 0x98BA, 65537, 0x1000000, 6)
}

CRC16CCITTTokenLetter(letter) {
    crc := 0xFFFF
    b := Ord(letter)
    crc := crc ^ (b << 8)
    Loop 8 {
        if (crc & 0x8000)
            crc := ((crc << 1) ^ 0x1021) & 0xFFFF
        else
            crc := (crc << 1) & 0xFFFF
    }
    return Format("{:04X} ", crc)
}

PunycodeAsciiTokenLetter(letter) {
    return "xn--" . Format("{:02x}", Ord(letter)) . " "
}

ZeroWidthBinaryVisibleLetter(letter) {
    bits := ToBinaryWidth(Ord(letter), 8)
    return "[ZW:" . StrReplace(StrReplace(bits, "0", "ZWSP"), "1", "ZWNJ") . "] "
}

InvisibleUnicodeVisibleLetter(letter) {
    bits := ToBinaryWidth(Ord(letter), 8)
    return "[INV:" . StrReplace(StrReplace(bits, "0", "WJ"), "1", "FA") . "] "
}

ROT18AlphaLetter(letter) {
    return ShiftLetter(letter, 13)
}

KnockCodeLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    r := Floor((n - 1) / 5) + 1
    c := Mod(n - 1, 5) + 1
    return RepeatChar("*", r) . " " . RepeatChar("*", c) . " / "
}

MorseFractionatedADFGXLetter(letter) {
    m := MorseLetter(letter)
    bits := StrReplace(StrReplace(m, ".", "A"), "-", "D")
    return StrReplace(bits, " ", "X") . " "
}

MorseSyllableTokenLetter(letter) {
    m := MorseLetter(letter)
    token := StrReplace(StrReplace(m, ".", "di"), "-", "dah")
    return StrReplace(token, " ", "-") . " "
}

GoldBugCipherSymbolLetter(letter) {
    symbols := ["5","2","-","8","1","3","4","6","0","9","*","†","‡","(",")",";",":","?","¶","]","[","&","@","$","%","#"]
    return symbols[LetterIndex(StrUpper(letter)) + 1] . " "
}

RosicrucianSymbolLetter(letter) {
    symbols := ["⊓","⊔","⊏","⊐","⊕","⊖","⊗","⊘","⊙","△","▽","◇","◆","○","●","□","■","◁","▷","◌","◍","◉","◎","◈","◊","◐"]
    return symbols[LetterIndex(StrUpper(letter)) + 1] . " "
}

TemplarSymbolLetter(letter) {
    symbols := ["⌜","⌝","⌞","⌟","┌","┐","└","┘","╳","╱","╲","◇","◆","△","▽","□","■","○","●","☩","✠","✚","✙","✛","✜","✢"]
    return symbols[LetterIndex(StrUpper(letter)) + 1] . " "
}

MalachimTokenLetter(letter) {
    return "[mal-" . StrUpper(letter) . "] "
}

CelestialTokenLetter(letter) {
    return "[cel-" . StrUpper(letter) . "] "
}

EnochianTokenLetter(letter) {
    return "[eno-" . StrUpper(letter) . "] "
}

PhoenicianLetter(letter) {
    idx := Mod(LetterIndex(StrUpper(letter)), 22)
    return Chr(0x10900 + idx) . " "
}

UgariticCuneiformLetter(letter) {
    return Chr(0x10380 + LetterIndex(StrUpper(letter))) . " "
}

EtruscanTokenLetter(letter) {
    return "[etr-" . StrUpper(letter) . "] "
}

GothicLetter(letter) {
    return Chr(0x10330 + LetterIndex(StrUpper(letter))) . " "
}

CopticLetter(letter) {
    letters := ["Ⲁ","Ⲃ","Ⲥ","Ⲇ","Ⲉ","Ϥ","Ⲅ","Ϩ","Ⲓ","Ϫ","Ⲕ","Ⲗ","Ⲙ","Ⲛ","Ⲟ","Ⲡ","Ϭ","Ⲣ","Ⲥ","Ⲧ","Ⲩ","Ⲫ","Ⲱ","Ϧ","ϒ","Ⲍ"]
    return letters[LetterIndex(StrUpper(letter)) + 1] . " "
}

AngloSaxonRuneLetter(letter) {
    runes := ["ᚠ","ᚢ","ᚦ","ᚩ","ᚱ","ᚳ","ᚷ","ᚹ","ᚻ","ᚾ","ᛁ","ᛄ","ᛇ","ᛈ","ᛉ","ᛋ","ᛏ","ᛒ","ᛖ","ᛗ","ᛚ","ᛝ","ᛟ","ᛞ","ᚪ","ᚫ"]
    return runes[LetterIndex(StrUpper(letter)) + 1] . " "
}

BaudotTapeHolesLetter(letter) {
    code := BaudotLetter(letter)
    return StrReplace(StrReplace(code, "1", "●"), "0", "○") . " "
}

MurrayPunchedTapeLetter(letter) {
    bits := ToBinaryWidth(Ord(letter), 5)
    return "|" . StrReplace(StrReplace(bits, "1", "●"), "0", "·") . "| "
}

HollerithPunchCodeLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    row := Floor((n - 1) / 3)
    col := Mod(n - 1, 3) + 1
    return "R" . row . "C" . col . " "
}

EBCDICDecimalLetter(letter) {
    ; Common uppercase EBCDIC ranges: A-I C1-C9, J-R D1-D9, S-Z E2-E9.
    idx := LetterIndex(StrUpper(letter))
    if idx < 9
        code := 0xC1 + idx
    else if idx < 18
        code := 0xD1 + (idx - 9)
    else
        code := 0xE2 + (idx - 18)
    return code . " "
}

IBMCardRowPunchLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    zone := n <= 9 ? "12" : n <= 18 ? "11" : "0"
    digit := Mod(n - 1, 9) + 1
    return zone . "-" . digit . " "
}

BaconianSlashLetter(letter) {
    bits := ToBinaryWidth(LetterIndex(StrUpper(letter)), 5)
    return StrReplace(StrReplace(bits, "0", "/"), "1", "\\") . " "
}

BaconianHighLowLetter(letter) {
    bits := ToBinaryWidth(LetterIndex(StrUpper(letter)), 5)
    return StrReplace(StrReplace(bits, "0", "L"), "1", "H") . " "
}

PolybiusCheckerAELetter(letter) {
    n := LetterIndex(StrUpper(letter))
    labels := "ABCDE"
    return SubStr(labels, Floor(n / 5) + 1, 1) . SubStr(labels, Mod(n, 5) + 1, 1) . " "
}

PolybiusChecker04Letter(letter) {
    n := LetterIndex(StrUpper(letter))
    return Floor(n / 5) . Mod(n, 5) . " "
}

TapCodeKnocksLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return RepeatChar("knock", Floor((n - 1) / 5) + 1) . " / " . RepeatChar("knock", Mod(n - 1, 5) + 1) . " | "
}

PrisonTapCodeLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    return "(" . (Floor((n - 1) / 5) + 1) . "," . (Mod(n - 1, 5) + 1) . ") "
}

FractionatedTapCodeLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    r := Floor((n - 1) / 5) + 1
    c := Mod(n - 1, 5) + 1
    return ToBinaryWidth(r, 3) . ToBinaryWidth(c, 3) . " "
}

BifidCoordinateStreamLetter(letter) {
    n := LetterIndex(StrUpper(letter))
    return (Floor(n / 5) + 1) . ":" . (Mod(n, 5) + 1) . " "
}

TrifidCoordinateStreamLetter(letter) {
    n := LetterIndex(StrUpper(letter))
    layer := Floor(n / 9) + 1
    rem := Mod(n, 9)
    return layer . ":" . (Floor(rem / 3) + 1) . ":" . (Mod(rem, 3) + 1) . " "
}

NihilistPlusKeyStreamLetter(letter) {
    global streamIndex, keyText
    n := LetterIndex(StrUpper(letter))
    p := (Floor(n / 5) + 1) * 10 + Mod(n, 5) + 1
    k := KeyShiftAt(keyText, streamIndex) + 11
    streamIndex += 1
    return (p + k) . " "
}

HillCoordinateTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter))
    return "[" . n . "," . Mod(n * 3 + 7, 26) . "] "
}

ModularInverseIndexLetter(letter) {
    n := LetterIndex(StrUpper(letter)) + 1
    vals := StrSplit("1|--|9|--|21|--|15|--|3|--|19|--|--|--|7|--|23|--|11|--|5|--|17|--|25|--", "|")
    return vals[n] . " "
}

AffineFamilyTokenLetter(letter) {
    n := LetterIndex(StrUpper(letter))
    return Format("a5b8:{:02d} ", Mod(5 * n + 8, 26))
}

OTPNumericTokenLetter(letter) {
    global streamIndex
    n := LetterIndex(StrUpper(letter))
    k := Mod((streamIndex * 17) + 23, 26)
    streamIndex += 1
    return Format("{:02d} ", Mod(n + k, 26))
}

VernamBitmaskTokenLetter(letter) {
    global streamIndex
    b := Ord(letter)
    k := Mod((streamIndex * 73) + 41, 256)
    streamIndex += 1
    return Format("{:02X} ", b ^ k)
}

RC4KeystreamTokenLetter(letter) {
    global streamIndex
    b := Ord(letter)
    k := Mod((streamIndex * 251 + 13) * 17, 256)
    streamIndex += 1
    return Format("{:02X} ", b ^ k)
}

ChaChaToyTokenLetter(letter) {
    global streamIndex
    k := Mod((streamIndex + 1) * 0x9E + 0x37, 256)
    streamIndex += 1
    return Format("{:02X} ", Ord(letter) ^ k)
}

SalsaToyTokenLetter(letter) {
    global streamIndex
    k := Mod((streamIndex + 5) * 0x7D + 0x2A, 256)
    streamIndex += 1
    return Format("{:02X} ", Ord(letter) ^ k)
}

Z85IndexLetter(letter) {
    alph := "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ.-:+=^!/*?&<>()[]{}@%$#"
    idx := LetterIndex(StrUpper(letter)) + 1
    return SubStr(alph, idx, 1) . " "
}

Bech32IndexLetter(letter) {
    alph := "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
    idx := LetterIndex(StrUpper(letter)) + 1
    return SubStr(alph, idx, 1) . " "
}

ZBase32IndexLetter(letter) {
    alph := "ybndrfg8ejkmcpqxot1uwisza345h769"
    idx := LetterIndex(StrUpper(letter)) + 1
    return SubStr(alph, idx, 1) . " "
}

CrockfordByteTokenLetter(letter) {
    alph := "0123456789ABCDEFGHJKMNPQRSTVWXYZ"
    b := Ord(letter)
    hi := Floor(b / 32)
    lo := Mod(b, 32)
    return SubStr(alph, hi + 1, 1) . SubStr(alph, lo + 1, 1) . " "
}


; ------------------------------------------------------------
; v20 additional live ciphers / encodings
; ------------------------------------------------------------

V20ExtraLetter(letter, variant) {
    global shiftValue, keyText, streamIndex, affineA, affineB
    u := StrUpper(letter)
    idx := LetterIndex(u)

    switch variant {
        case "Caesar reverse alphabet shift":
            return V20ReversedAlphabetShift(letter, shiftValue)
        case "Atbash Caesar shift":
            return ShiftLetter(AtbashLetter(letter), shiftValue)
        case "ROT13 then Atbash":
            return AtbashLetter(ShiftLetter(letter, 13))
        case "Vigenere reversed alphabet":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return V20ReversedAlphabetShift(letter, k)
        case "Beaufort reversed alphabet":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return V20ReversedAlphabetFromIndex(letter, PositiveMod(k - idx, 26))
        case "Gronsfeld reversed alphabet":
            k := DigitShiftAt(keyText, streamIndex), streamIndex += 1
            return V20ReversedAlphabetShift(letter, k)
        case "Autokey reversed alphabet":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return V20ReversedAlphabetShift(letter, k)
        case "Progressive key Beaufort":
            k := KeyShiftAt(keyText, streamIndex) + streamIndex, streamIndex += 1
            return LetterFromIndex(PositiveMod(k - idx, 26), IsUpperLetter(letter))
        case "Interrupted Beaufort":
            k := KeyShiftAt(keyText, Mod(streamIndex, 5)), streamIndex += 1
            return LetterFromIndex(PositiveMod(k - idx, 26), IsUpperLetter(letter))
        case "Keyed Beaufort":
            alpha := KeywordAlphabet(keyText)
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return V20MapAlphaIndex(letter, alpha, PositiveMod(k - idx, 26))
        case "Keyed Variant Beaufort":
            alpha := KeywordAlphabet(keyText)
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return V20MapAlphaIndex(letter, alpha, PositiveMod(idx - k, 26))
        case "Slide Vigenere":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, k + shiftValue)
        case "Diana reciprocal":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return LetterFromIndex(PositiveMod(25 - idx - k, 26), IsUpperLetter(letter))
        case "Vigenere Fibonacci stream":
            k := V20Fibonacci(Mod(streamIndex, 20)) + KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, k)
        case "Vigenere Lucas stream":
            k := V20Lucas(Mod(streamIndex, 20)) + KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, k)
        case "Vigenere prime stream":
            k := V20PrimeAt(streamIndex) + KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, k)
        case "Vigenere triangular stream":
            k := V20Triangular(streamIndex + 1) + KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, k)
        case "Multiplicative progressive":
            aVals := [3,5,7,11,17,25]
            a := aVals[Mod(streamIndex, aVals.Length) + 1], streamIndex += 1
            return LetterFromIndex(PositiveMod(idx * a, 26), IsUpperLetter(letter))
        case "Affine with key shift":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return LetterFromIndex(PositiveMod(affineA * idx + affineB + k, 26), IsUpperLetter(letter))
        case "Caesar keyed stream":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, shiftValue + k)
        case "Porta progressive reverse":
            k := Floor((KeyShiftAt(keyText, streamIndex) + streamIndex) / 2), streamIndex += 1
            y := idx < 13 ? PositiveMod(idx + k, 13) + 13 : PositiveMod(idx - 13 - k, 13)
            return LetterFromIndex(y, IsUpperLetter(letter))
        case "Trithemius descending":
            k := -streamIndex, streamIndex += 1
            return ShiftLetter(letter, k)
        case "Polybius row letters":
            r := Floor(idx / 5)
            return SubStr("ABCDE", r + 1, 1) . (Mod(idx, 5) + 1) . " "
        case "Polybius column letters":
            r := Floor(idx / 5), c := Mod(idx, 5)
            return (r + 1) . SubStr("ABCDE", c + 1, 1) . " "
        case "Polybius chess coords":
            return Chr(65 + Mod(idx, 5)) . (Floor(idx / 5) + 1) . " "
        case "Polybius barcode token":
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return RepeatChar("|", r) . "." . RepeatChar("|", c) . " "
        case "Polybius binary coords":
            r := Floor(idx / 5), c := Mod(idx, 5)
            return V20PadLeft(BaseN(r, 2), 3, "0") . V20PadLeft(BaseN(c, 2), 3, "0") . " "
        case "Bifid raw coords":
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return "R" . r . "C" . c . " "
        case "Trifid raw coords":
            layer := Floor(idx / 9) + 1, rest := Mod(idx, 9)
            return layer . ":" . (Floor(rest / 3) + 1) . ":" . (Mod(rest, 3) + 1) . " "
        case "ADFGX spaced":
            labels := "ADFGX", r := Floor(idx / 5), c := Mod(idx, 5)
            return SubStr(labels, r + 1, 1) . " " . SubStr(labels, c + 1, 1) . " "
        case "ADFGVX spaced":
            labels := "ADFGVX", r := Floor(idx / 6), c := Mod(idx, 6)
            return SubStr(labels, r + 1, 1) . " " . SubStr(labels, c + 1, 1) . " "
        case "Nihilist keyed number":
            k := KeyShiftAt(keyText, streamIndex) + 11, streamIndex += 1
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return ((r * 10 + c) + k) . " "
        case "Checkerboard serial":
            return Format("CB{:02d} ", idx + 1)
        case "Tap binary token":
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return V20PadLeft(BaseN(r, 2), 3, "0") . "." . V20PadLeft(BaseN(c, 2), 3, "0") . " "
        case "Knock binary token":
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return RepeatChar("1", r) . "0" . RepeatChar("1", c) . " "
        case "Baconian 12345":
            return V20BaconianCustom(idx, "1", "2")
        case "Baconian emoji":
            return V20BaconianCustom(idx, "○", "●")
        case "Baconian morse":
            return V20BaconianCustom(idx, ".", "-")
        case "Baconian Roman":
            return V20BaconianCustom(idx, "I", "V")
        case "LCG stream hex":
            k := Mod((streamIndex * 1103515245 + 12345) >> 8, 256), streamIndex += 1
            return Format("{:02X} ", Ord(letter) ^ k)
        case "Xorshift stream hex":
            k := V20XorShiftByte(streamIndex + 1), streamIndex += 1
            return Format("{:02X} ", Ord(letter) ^ k)
        case "Blum Blum Shub toy":
            k := Mod((streamIndex + 7) * (streamIndex + 7), 77), streamIndex += 1
            return Format("{:02X} ", Ord(letter) ^ k)
        case "Fibonacci LFSR toy":
            k := Mod(V20Fibonacci(Mod(streamIndex, 20)) * 13 + 7, 256), streamIndex += 1
            return Format("{:02X} ", Ord(letter) ^ k)
        case "Vernam decimal byte":
            k := Mod((streamIndex * 73) + 41, 256), streamIndex += 1
            return Format("{:03d} ", Ord(letter) ^ k)
        case "OTP base26 token":
            k := Mod((streamIndex * 17) + 23, 26), streamIndex += 1
            return LetterFromIndex(PositiveMod(idx + k, 26), true) . Format("{:02d} ", k)
        case "Running key numeric":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return Format("{:02d} ", PositiveMod(idx + k, 26))
        case "Base24 index":
            return V20BaseIndex(letter, 24)
        case "Base30 index":
            return V20BaseIndex(letter, 30)
        case "Base64 index":
            return V20BaseIndex(letter, 64)
        case "Base85 index":
            return V20BaseIndex(letter, 85)
        case "ASCII base3 byte":
            return V20BaseByte(letter, 3)
        case "ASCII base4 byte":
            return V20BaseByte(letter, 4)
        case "ASCII base5 byte":
            return V20BaseByte(letter, 5)
        case "ASCII base6 byte":
            return V20BaseByte(letter, 6)
        case "ASCII base12 byte":
            return V20BaseByte(letter, 12)
        case "ASCII base36 byte":
            return V20BaseByte(letter, 36)
        case "UTF-8 bytes decimal":
            return Ord(letter) . " "
        case "UTF-8 bytes hex spaced":
            return Format("{:02X} ", Ord(letter))
        case "Java unicode escape":
            return "\\u" . Format("{:04X} ", Ord(letter))
        case "Python unicode escape":
            return "\\u" . Format("{:04x} ", Ord(letter))
        case "CSharp unicode escape":
            return "\\u" . Format("{:04X} ", Ord(letter))
        case "CSS unicode padded":
            return "\\" . Format("{:06X} ", Ord(letter))
        case "SQL CHAR token":
            return "CHAR(" . Ord(letter) . ") "
        case "PowerShell char token":
            return "[char]" . Ord(letter) . " "
        case "Decimal entity padded":
            return "&#" . Format("{:05d}", Ord(letter)) . "; "
        case "Hex entity padded":
            return "&#x" . Format("{:04X}", Ord(letter)) . "; "
        case "Percent lowercase":
            return "%" . Format("{:02x} ", Ord(letter))
        case "Percent uppercase spaced":
            return "%" . Format("{:02X} ", Ord(letter))
        case "Quoted printable soft token":
            return "=" . Format("{:02X}_", Ord(letter))
        case "Morse prosign token":
            return "<" . StrReplace(Trim(MorseLetter(letter)), " ", "") . "> "
        case "NATO initials only":
            return SubStr(NatoLetter(letter), 1, 1) . " "
        case "Pigpen grid code":
            r := Floor(idx / 9) + 1, c := Mod(idx, 9) + 1
            return "P" . r . c . " "
        case "Templar cross code":
            return "+" . Format("{:02d} ", idx + 1)
        case "Semaphore compass":
            dirs := ["N","NE","E","SE","S","SW","W","NW"]
            return dirs[Mod(idx, 8) + 1] . ":" . dirs[Mod(Floor(idx / 8) + 2, 8) + 1] . " "
        case "Braille dots token":
            patterns := ["1","12","14","145","15","124","1245","125","24","245","13","123","134","1345","135","1234","12345","1235","234","2345","136","1236","2456","1346","13456","1356"]
            return "⠿" . patterns[idx + 1] . " "
        case "Moon phase alphabet":
            arr := ["🌑","🌒","🌓","🌔","🌕","🌖","🌗","🌘"]
            return arr[Mod(idx, arr.Length) + 1] . Format("{:02d} ", Floor(idx / arr.Length))
        case "Planet sequence alphabet":
            arr := ["☿","♀","♁","♂","♃","♄","♅","♆","♇"]
            return arr[Mod(idx, arr.Length) + 1] . Format("{:02d} ", Floor(idx / arr.Length))
        case "Diceware coordinate token":
            n := idx + 11
            return "D" . Floor(n / 6) . Mod(n, 6) . " "
    }
    return letter
}

V20ReversedAlphabetShift(letter, shift) {
    rev := "ZYXWVUTSRQPONMLKJIHGFEDCBA"
    pos := InStr(rev, StrUpper(letter)) - 1
    mapped := SubStr(rev, PositiveMod(pos + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

V20ReversedAlphabetFromIndex(letter, idx) {
    rev := "ZYXWVUTSRQPONMLKJIHGFEDCBA"
    mapped := SubStr(rev, PositiveMod(idx, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

V20MapAlphaIndex(letter, alpha, idx) {
    mapped := SubStr(alpha, PositiveMod(idx, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

V20Fibonacci(n) {
    a := 0, b := 1
    Loop n {
        t := a + b
        a := b
        b := t
    }
    return a
}

V20Lucas(n) {
    a := 2, b := 1
    if n = 0
        return a
    Loop n {
        t := a + b
        a := b
        b := t
    }
    return a
}

V20PrimeAt(n) {
    primes := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79]
    return primes[Mod(n, primes.Length) + 1]
}

V20Triangular(n) {
    return Floor(n * (n + 1) / 2)
}

V20PadLeft(text, width, ch := "0") {
    text := "" . text
    if StrLen(text) >= width
        return text
    return RepeatChar(ch, width - StrLen(text)) . text
}

V20BaconianCustom(idx, a, b) {
    bits := V20PadLeft(BaseN(idx, 2), 5, "0")
    return StrReplace(StrReplace(bits, "0", a), "1", b) . " "
}

V20XorShiftByte(seed) {
    x := seed & 0xFFFFFFFF
    x := x ^ ((x << 13) & 0xFFFFFFFF)
    x := x ^ (x >> 17)
    x := x ^ ((x << 5) & 0xFFFFFFFF)
    return x & 0xFF
}

V20BaseIndex(letter, base) {
    n := LetterIndex(StrUpper(letter)) + 1
    return V20EncodeBase(n, base) . " "
}

V20BaseByte(letter, base) {
    return V20EncodeBase(Ord(letter), base) . " "
}

V20EncodeBase(n, base) {
    digits := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/!#$%&()*+-;<=>?@^_`{|}~"
    base := Integer(base)
    if base < 2
        base := 2
    if base > StrLen(digits)
        base := StrLen(digits)
    if n = 0
        return "0"
    out := ""
    while n > 0 {
        r := Mod(n, base)
        out := SubStr(digits, r + 1, 1) . out
        n := Floor(n / base)
    }
    return out
}

; ------------------------------------------------------------
; v21 additional live ciphers / encodings
; ------------------------------------------------------------

V21ExtraLetter(letter, mode) {
    global streamIndex, keyText, shiftValue, affineA, affineB
    u := StrUpper(letter)
    idx := LetterIndex(u)
    isUpper := IsUpperLetter(letter)

    switch mode {
        case "Reciprocal Vigenere":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return LetterFromIndex(PositiveMod(k - idx, 26), isUpper)
        case "Reciprocal Gronsfeld":
            k := DigitShiftAt(keyText, streamIndex), streamIndex += 1
            return LetterFromIndex(PositiveMod(k - idx, 26), isUpper)
        case "Beaufort Fibonacci stream":
            k := Mod(V20Fibonacci(Mod(streamIndex, 20)), 26), streamIndex += 1
            return LetterFromIndex(PositiveMod(k - idx, 26), isUpper)
        case "Beaufort prime stream":
            k := Mod(V20PrimeAt(streamIndex), 26), streamIndex += 1
            return LetterFromIndex(PositiveMod(k - idx, 26), isUpper)
        case "Variant Beaufort Fibonacci":
            k := Mod(V20Fibonacci(Mod(streamIndex, 20)), 26), streamIndex += 1
            return ShiftLetter(letter, -k)
        case "Variant Beaufort prime":
            k := Mod(V20PrimeAt(streamIndex), 26), streamIndex += 1
            return ShiftLetter(letter, -k)
        case "Autokey Caesar stream":
            k := PositiveMod(shiftValue + streamIndex + idx, 26), streamIndex += 1
            return ShiftLetter(letter, k)
        case "Progressive Atbash stream":
            k := streamIndex, streamIndex += 1
            return ShiftLetter(AtbashLetter(letter), k)
        case "Keyed Polybius 0-4":
            return V21KeyedPolybiusCoord(letter, "01234", "01234")
        case "Keyed Polybius A-E":
            return V21KeyedPolybiusCoord(letter, "ABCDE", "ABCDE")
        case "Keyed Tap coordinate":
            return V21KeyedPolybiusCoord(letter, "12345", "12345")
        case "ADFGX numeric labels":
            return V21PlainCoord(letter, "12345", 5)
        case "ADFGVX numeric labels":
            return V21PlainCoord6(letter, "123456")
        case "Polybius mixed 6x6 keyed":
            return V21KeyedPolybius6(letter, "123456", "123456")
        case "Checkerboard 10x10 token":
            return Format("{}{} ", Floor(Ord(letter) / 10), Mod(Ord(letter), 10))
        case "VIC chain addition toy":
            k := Mod((streamIndex ? streamIndex : 1) + idx + KeyShiftAt(keyText, streamIndex), 10), streamIndex += 1
            return Format("{}{} ", idx + 1, k)
        case "Nihilist zero padded":
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return Format("{:02d} ", r * 10 + c)
        case "Nihilist keyed hex":
            k := KeyShiftAt(keyText, streamIndex) + 11, streamIndex += 1
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return Format("{:02X} ", r * 10 + c + k)
        case "Bifid split token":
            r := Floor(idx / 5) + 1, c := Mod(idx, 5) + 1
            return "B[" . r . "][" . c . "] "
        case "Trifid layer token":
            layer := Floor(idx / 9) + 1, rem := Mod(idx, 9)
            return "T" . layer . "-" . (Floor(rem / 3) + 1) . "-" . (Mod(rem, 3) + 1) . " "
        case "Playfair digraph marker":
            return "PF(" . u . "X) "
        case "Hill mod26 vector token":
            return "H[" . idx . "," . Mod(idx * 5 + 8, 26) . "] "
        case "Modular square index":
            return Format("{:02d} ", Mod((idx + 1) * (idx + 1), 26))
        case "Modular cube index":
            n := idx + 1
            return Format("{:02d} ", Mod(n * n * n, 26))
        case "Power residue index":
            n := idx + 1
            return Format("{:02d} ", Mod(n * n * n * n * n, 26))
        case "Quadratic residue token":
            n := idx + 1
            return "QR" . Format("{:02d} ", Mod(n * n, 29))
        case "QR format bits token":
            return "QR:" . ToBinaryWidth(Mod(idx * 7973 + 0x5412, 32768), 15) . " "
        case "Aztec barcode token":
            return "AZ" . V20PadLeft(V20EncodeBase(idx + 1, 32), 2, "0") . " "
        case "PDF417 codeword token":
            return "PDF" . Format("{:03d} ", Mod((idx + 1) * 29 + 17, 929))
        case "DataMatrix codeword token":
            return "DM" . Format("{:03d} ", Ord(letter) + 1)
        case "Code93 token":
            return "C93(" . u . ") "
        case "MSI check token":
            return "MSI" . (idx + 1) . V21Mod10Check(idx + 1) . " "
        case "Interleaved 2 of 5 pair":
            n := Format("{:02d}", idx + 1)
            return "I25:" . n . " "
        case "POSTNET digit token":
            return V21PostnetToken(Mod(idx, 10), "POST")
        case "PLANET digit token":
            return V21PostnetToken(Mod(idx, 10), "PLANET")
        case "Royal Mail 4-state token":
            return "RM" . V21FourState(idx, "TADF") . " "
        case "KIX 4-state token":
            return "KIX" . V21FourState(idx, "ADFT") . " "
        case "Facing identification mark":
            return "FIM-" . SubStr("ABCDE", Mod(idx, 5) + 1, 1) . " "
        case "OCR-A token":
            return "[OCR-A:" . u . "] "
        case "MICR E13B token":
            return "[MICR:" . u . "] "
        case "MIME quoted word Q":
            return "=?UTF-8?Q?=" . Format("{:02X}", Ord(letter)) . "?= "
        case "MIME quoted word B":
            return "=?UTF-8?B?" . Base64PerLetter(letter) . "?= "
        case "LDAP hex escape":
            return "\" . Format("{:02X}", Ord(letter))
        case "Regex unicode escape":
            return "\x{" . Format("{:X}", Ord(letter)) . "}"
        case "XML CDATA token":
            return "<![CDATA[" . letter . "]]>"
        case "CSV quoted token":
            return Chr(34) . letter . Chr(34) . ","
        case "Shell ANSI C escape":
            return "\x" . Format("{:02X}", Ord(letter))
        case "Bash hex token":
            return "$'\x" . Format("{:02X}", Ord(letter)) . "' "
        case "Python bytes token":
            return "b'\x" . Format("{:02X}", Ord(letter)) . "' "
        case "Ruby hex token":
            return "\x" . Format("{:02X}", Ord(letter)) . " "
        case "Perl hex token":
            return "\x{" . Format("{:X}", Ord(letter)) . "} "
        case "Go rune token":
            return "'\\u" . Format("{:04X}", Ord(letter)) . "' "
        case "Rust unicode token":
            return "'\\u{" . Format("{:X}", Ord(letter)) . "}' "
        case "HTML named fallback":
            return "&" . u . "opf; "
        case "SGML entity token":
            return "&char" . Ord(letter) . "; "
        case "TeX char token":
            return "\\char" . Ord(letter) . " "
        case "PostScript char token":
            return "(" . letter . ") show "
        case "Assembly DB hex":
            return "DB 0x" . Format("{:02X}", Ord(letter)) . " "
        case "Intel asm char":
            return "BYTE " . Format("{:02X}h ", Ord(letter))
        case "MIPS ascii byte":
            return ".byte 0x" . Format("{:02X} ", Ord(letter))
        case "Byte pair hex token":
            b := Ord(letter)
            return Format("{:02X}:{:02X} ", b, b ^ 0xFF)
        case "Nibble swap hex":
            return Format("{:02X} ", V21NibbleSwap(Ord(letter)))
        case "Bit reverse byte":
            return Format("{:02X} ", V21BitReverse8(Ord(letter)))
        case "Gray code reflected":
            b := Ord(letter)
            return ToBinaryWidth(b ^ (b >> 1), 8) . " "
        case "Excess-3 BCD token":
            return V21BcdDigitToken(idx + 1, 3)
        case "BCD 2421 token":
            return V21BcdWeighted(idx + 1, "2421")
        case "BCD 5211 token":
            return V21BcdWeighted(idx + 1, "5211")
        case "Johnson code token":
            return V21JohnsonCode(Mod(idx, 10)) . " "
        case "One-hot index token":
            return V21OneHot(Mod(idx, 8)) . " "
        case "Two-hot index token":
            return V21TwoHot(Mod(idx, 8)) . " "
        case "Huffman toy token":
            return V21ToyPrefixCode(idx, "H")
        case "Shannon-Fano toy token":
            return V21ToyPrefixCode(25 - idx, "SF")
        case "Morse American token":
            return V21AmericanMorseLetter(letter)
        case "Chappe semaphore token":
            return "CH" . (Floor(idx / 6) + 1) . "-" . (Mod(idx, 6) + 1) . " "
        case "Optical telegraph token":
            return "OPT[" . (Floor(idx / 10) + 1) . ":" . (Mod(idx, 10) + 1) . "] "
        case "Navajo code talker token":
            return V21CodeWord(letter, V21NavajoWords())
        case "Commercial code word":
            return V21CodeWord(letter, V21CommercialWords())
        case "Telegraph code word":
            return V21CodeWord(letter, V21TelegraphWords())
        case "Postal abbreviation token":
            return V21CodeWord(letter, V21PostalWords())
        case "Weather code token":
            return "WX" . Format("{:02d} ", idx + 1)
    }
    return letter
}

V21PlainCoord(letter, labels, size) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / size)
    c := Mod(idx, size)
    return SubStr(labels, r + 1, 1) . SubStr(labels, c + 1, 1) . " "
}

V21PlainCoord6(letter, labels) {
    idx := LetterIndex(StrUpper(letter))
    return SubStr(labels, Floor(idx / 6) + 1, 1) . SubStr(labels, Mod(idx, 6) + 1, 1) . " "
}

V21KeyedPolybiusCoord(letter, rowLabels, colLabels) {
    global keyText
    alpha := KeywordAlphabet(keyText)
    pos := InStr(alpha, StrUpper(letter)) - 1
    if pos < 0
        pos := LetterIndex(StrUpper(letter))
    r := Floor(pos / 5)
    c := Mod(pos, 5)
    return SubStr(rowLabels, r + 1, 1) . SubStr(colLabels, c + 1, 1) . " "
}

V21KeyedPolybius6(letter, rowLabels, colLabels) {
    global keyText
    alpha := KeywordAlphabet(keyText) . "0123456789"
    pos := InStr(alpha, StrUpper(letter)) - 1
    if pos < 0
        pos := LetterIndex(StrUpper(letter))
    r := Floor(pos / 6)
    c := Mod(pos, 6)
    return SubStr(rowLabels, r + 1, 1) . SubStr(colLabels, c + 1, 1) . " "
}

V21Mod10Check(n) {
    n := Integer(n)
    s := 0
    Loop Parse, (n . "") {
        d := Integer(A_LoopField)
        if Mod(A_Index, 2) = 1
            d *= 2
        if d > 9
            d -= 9
        s += d
    }
    return Mod(10 - Mod(s, 10), 10)
}

V21PostnetToken(digit, prefix) {
    patterns := ["11000","00011","00101","00110","01001","01010","01100","10001","10010","10100"]
    return prefix . ":" . StrReplace(StrReplace(patterns[digit + 1], "1", "|"), "0", ".") . " "
}

V21FourState(value, states) {
    value := Integer(value)
    out := ""
    Loop 4 {
        r := Mod(value, 4)
        out := SubStr(states, r + 1, 1) . out
        value := Floor(value / 4)
    }
    return out
}

V21BcdDigitToken(n, add := 0) {
    n := Integer(n)
    tens := Floor(n / 10)
    ones := Mod(n, 10)
    return ToBinaryWidth(tens + add, 4) . " " . ToBinaryWidth(ones + add, 4) . " "
}

V21BcdWeighted(n, weights) {
    n := Mod(Integer(n), 10)
    if weights = "2421" {
        table := ["0000","0001","0010","0011","0100","1011","1100","1101","1110","1111"]
    } else {
        table := ["0000","0001","0010","0011","0111","1000","1100","1101","1110","1111"]
    }
    return table[n + 1] . " "
}

V21JohnsonCode(n) {
    n := Mod(Integer(n), 10)
    arr := ["00000","10000","11000","11100","11110","11111","01111","00111","00011","00001"]
    return arr[n + 1]
}

V21OneHot(n) {
    n := Mod(Integer(n), 8)
    out := ""
    Loop 8
        out .= ((A_Index - 1 = n) ? "1" : "0")
    return out
}

V21TwoHot(n) {
    n := Mod(Integer(n), 8)
    out := ""
    Loop 8 {
        p := A_Index - 1
        out .= ((p = n || p = Mod(n + 1, 8)) ? "1" : "0")
    }
    return out
}

V21ToyPrefixCode(idx, prefix) {
    length := Floor(idx / 5) + 2
    code := V20PadLeft(V20EncodeBase(Mod(idx, 5), 2), length, "0")
    return prefix . code . " "
}

V21AmericanMorseLetter(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    codes := StrSplit(".-|-...|.. .|-..|.|.-.|--.|....|..|-.-.|-.-|.-..|--|-.|. .|.....|..-.|. ..|...|-|..-|...-|.--|.-..|.. ..|... .", "|")
    return (idx >= 1 && idx <= codes.Length) ? codes[idx] . " / " : letter
}

V21CodeWord(letter, words) {
    idx := LetterIndex(StrUpper(letter)) + 1
    return words[idx] . " "
}

V21NavajoWords() {
    return ["Wol-la-chee","Shush","Moasi","Be","Dzeh","Ma-e","Klizzie","Lin","Tkin","Tkele-cho-gi","Klizzie-yazzi","Dibeh-yazzi","Na-as-tso-si","Nesh-chee","Ne-ahs-jah","Bi-sodih","Ca-yeilth","Gah","Dibeh","Than-zie","No-da-ih","A-keh-di-glini","Gloe-ih","Al-an-as-dzoh","Tsah-as-zih","Besh-do-gliz"]
}

V21CommercialWords() {
    return ["Acme","Boston","Cargo","Delta","Edison","Federal","Global","Harbor","Imperial","Junction","Keystone","Liberty","Mercury","National","Oceanic","Pacific","Quantum","Reliable","Sterling","Transit","Union","Victory","Western","Xenia","Yardley","Zenith"]
}

V21TelegraphWords() {
    return ["Ack","Break","Copy","Dispatch","End","Figure","Go","Hold","Info","Join","Key","Line","Message","Number","Over","Priority","Query","Repeat","Stop","Transmit","Urgent","Verify","Wait","Xray","Yield","Zero"]
}

V21PostalWords() {
    return ["AL","AK","AZ","AR","CA","CO","CT","DE","FL","GA","HI","IA","ID","IL","IN","KS","KY","LA","MA","MD","ME","MI","MN","MO","MS","MT"]
}

V21NibbleSwap(b) {
    b := Integer(b) & 0xFF
    return ((b & 0x0F) << 4) | ((b & 0xF0) >> 4)
}

V21BitReverse8(b) {
    b := Integer(b) & 0xFF
    out := 0
    Loop 8 {
        out := (out << 1) | (b & 1)
        b := b >> 1
    }
    return out
}



; ------------------------------------------------------------
; v22 additional live ciphers / encodings
; ------------------------------------------------------------

V22ExtraLetter(letter, mode) {
    global streamIndex, keyText, shiftValue
    u := StrUpper(letter)
    idx := LetterIndex(u)
    n := idx + 1
    isUpper := IsUpperLetter(letter)

    switch mode {
        case "Vigenere minus key":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(letter, -k)
        case "Vigenere plus Atbash":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return ShiftLetter(AtbashLetter(letter), k)
        case "Beaufort Atbash hybrid":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return LetterFromIndex(PositiveMod(k - (25 - idx), 26), isUpper)
        case "Variant Beaufort Atbash hybrid":
            k := KeyShiftAt(keyText, streamIndex), streamIndex += 1
            return LetterFromIndex(PositiveMod((25 - idx) - k, 26), isUpper)
        case "Caesar sine wave shift":
            p := streamIndex, streamIndex += 1
            return ShiftLetter(letter, Round(13 + 12 * Sin(p)))
        case "Caesar cosine wave shift":
            p := streamIndex, streamIndex += 1
            return ShiftLetter(letter, Round(13 + 12 * Cos(p)))
        case "Caesar sawtooth shift":
            p := streamIndex, streamIndex += 1
            return ShiftLetter(letter, Mod(p * 3 + shiftValue, 26))
        case "Caesar square wave shift":
            p := streamIndex, streamIndex += 1
            return ShiftLetter(letter, Mod(p, 2) ? 19 : 7)
        case "Caesar triangular wave shift":
            p := streamIndex, streamIndex += 1
            r := Mod(p, 26)
            return ShiftLetter(letter, r < 13 ? r : 26 - r)
        case "Prime gap Caesar shift":
            p := streamIndex + 1, streamIndex += 1
            return ShiftLetter(letter, V22PrimeGap(p))
        case "Pell Caesar shift", "Jacobsthal Caesar shift", "Padovan Caesar shift", "Tetranacci Caesar shift":
            p := streamIndex + 1, streamIndex += 1
            return ShiftLetter(letter, V22SequenceShift(mode, p))
        case "Keyed reciprocal substitution":
            alpha := KeywordAlphabet(keyText)
            p := InStr(alpha, u) - 1
            return LetterFromIndex(PositiveMod(25 - p, 26), isUpper)
        case "Keyed reverse substitution":
            alpha := KeywordAlphabet(keyText)
            return SubstituteFromAlphabet(letter, V22ReverseString(alpha))
        case "Keyword transposed alphabet":
            return SubstituteFromAlphabet(letter, V22KeywordTransposedAlphabet(keyText))
        case "Alphabet rail split":
            return SubstituteFromAlphabet(letter, "ACEGIKMOQSUWYBDFHJLNPRTVXZ")
        case "Alphabet odd-even split":
            return SubstituteFromAlphabet(letter, "BDFHJLNPRTVXZACEGIKMOQSUWY")
        case "Alphabet vowel-first":
            return SubstituteFromAlphabet(letter, "AEIOUBCDFGHJKLMNPQRSTVWXYZ")
        case "Alphabet consonant-first":
            return SubstituteFromAlphabet(letter, "BCDFGHJKLMNPQRSTVWXYZAEIOU")
        case "Alphabet frequency order":
            return SubstituteFromAlphabet(letter, "ETAOINSHRDLCUMWFGYPBVKJXQZ")
        case "Polybius Greek labels":
            return V22Coord(idx, "ΑΒΓΔΕ", 5, ".")
        case "Polybius Morse labels":
            return V22Coord(idx, ".-*/+", 5, "")
        case "Polybius Roman labels":
            return V22Coord(idx, "IVXLC", 5, ".")
        case "Polybius symbol coords":
            return V22Coord(idx, "★●◆▲■", 5, "")
        case "Polybius NATO coords":
            return V22NatoCoord(idx)
        case "Checkerboard phone coords":
            return V22PhoneCoord(letter)
        case "Checkerboard keyboard coords":
            return V22KeyboardCoord(letter)
        case "Checkerboard hex coords":
            return V22Coord(idx, "0123456789ABCDEF", 16, ":")
        case "ADFGX reversed square":
            return V22KeyedCoord(letter, V22ReverseString(ALPHABET), "ADFGX", 5)
        case "ADFGVX reversed square":
            return V22KeyedCoord6(letter, V22ReverseString("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"), "ADFGVX")
        case "Baconian Greek":
            return V22Bacon(idx, "α", "β", "")
        case "Baconian binary spaced":
            return V22Bacon(idx, "0 ", "1 ", "")
        case "Baconian quinary digits":
            return V22BaconQuinary(idx)
        case "Baconian 0-1 compact":
            return V22Bacon(idx, "0", "1", " ")
        case "Baconian braille":
            return V22Bacon(idx, "⠂", "⠄", " ")
        case "Baconian flag token":
            return V22Bacon(idx, "[W]", "[B]", " ")
        case "Morse Unicode symbols":
            return V22MorseReplace(letter, "·", "−", " ")
        case "Morse blocks":
            return V22MorseReplace(letter, "▁", "█", " ")
        case "Morse arrows":
            return V22MorseReplace(letter, "←", "→", " ")
        case "Morse vowels consonants":
            return V22MorseReplace(letter, "V", "C", " ")
        case "Morse word code":
            return V22MorseWordCode(letter)
        case "Morse phone taps":
            return V22MorsePhoneTaps(letter)
        case "Morse base3 token":
            return V22MorseBase3(letter)
        case "Morse length-dash-dot":
            raw := V22MorseRaw(letter)
            return StrLen(raw) . ":" . V22CountChar(raw, "-") . ":" . V22CountChar(raw, ".") . " "
        case "ASCII base13 byte":
            return V20EncodeBase(Ord(letter), 13) . " "
        case "ASCII base17 byte":
            return V20EncodeBase(Ord(letter), 17) . " "
        case "ASCII base19 byte":
            return V20EncodeBase(Ord(letter), 19) . " "
        case "ASCII base21 byte":
            return V20EncodeBase(Ord(letter), 21) . " "
        case "ASCII base23 byte":
            return V20EncodeBase(Ord(letter), 23) . " "
        case "ASCII base27 byte":
            return V20EncodeBase(Ord(letter), 27) . " "
        case "ASCII base31 byte":
            return V20EncodeBase(Ord(letter), 31) . " "
        case "ASCII base52 byte":
            return V20EncodeBase(Ord(letter), 52) . " "
        case "UTF-8 binary compact":
            return ToBinaryWidth(Ord(letter), 8) . " "
        case "UTF-8 hex colon":
            return Format("{:02X}:", Ord(letter))
        case "UTF-16BE decimal":
            return Floor(Ord(letter) / 256) . "," . Mod(Ord(letter), 256) . " "
        case "UTF-32LE decimal":
            cp := Ord(letter)
            return Mod(cp,256) . "," . Mod(Floor(cp/256),256) . "," . Mod(Floor(cp/65536),256) . "," . Mod(Floor(cp/16777216),256) . " "
        case "URI component token":
            return "%" . Format("{:02X}", Ord(letter))
        case "CSS escape short":
            return "\\" . Format("{:X}", Ord(letter)) . " "
        case "HTML entity hex padded":
            return "&#x" . V22PadLeft(Format("{:X}", Ord(letter)), 4, "0") . ";"
        case "XML entity decimal padded":
            return "&#" . V22PadLeft(Ord(letter), 5, "0") . ";"
        case "Base64 no padding per letter":
            return StrReplace(StrReplace(Trim(Base64PerLetter(letter)), "=", ""), " ", "") . " "
        case "Base32 no padding per letter":
            return V22Base32Letter(letter, false)
        case "Base85 ascii85 framed":
            return "<~" . V22Ascii85Byte(Ord(letter)) . "~> "
        case "Base91 index token":
            return "B91:" . V20EncodeBase(idx + 1, 91) . " "
        case "CRC4 token":
            return "C4:" . Format("{:X} ", V22CrcBits(Ord(letter), 4, 0x3))
        case "CRC5 USB token":
            return "C5:" . V22PadLeft(V20EncodeBase(V22CrcBits(Ord(letter), 5, 0x05), 2), 5, "0") . " "
        case "CRC6 token":
            return "C6:" . V22PadLeft(V20EncodeBase(V22CrcBits(Ord(letter), 6, 0x27), 2), 6, "0") . " "
        case "CRC7 token":
            return "C7:" . Format("{:02X} ", V22CrcBits(Ord(letter), 7, 0x09))
        case "CRC12 token":
            return "C12:" . Format("{:03X} ", V22CrcBits(Ord(letter), 12, 0x80F))
        case "CRC24 toy token":
            return "C24:" . Format("{:06X} ", V22Checksum24(Ord(letter)))
        case "LRC token":
            return "LRC:" . Format("{:02X} ", ((-Ord(letter)) & 0xFF))
        case "XOR checksum token":
            return "XOR:" . Format("{:02X} ", Ord(letter) ^ 0x5A)
        case "EAN-8 check token":
            return V22CheckNumber("EAN8", 7, idx + 1)
        case "Code11 check token":
            return V22CheckNumber("C11", 5, idx + 1)
        case "Pharmacode token":
            return "PH" . V22Pharmacode(idx + 1) . " "
        case "Telepen token":
            return "TP(" . Format("{:02X}", Ord(letter)) . ") "
        case "Maxicode word token":
            return "MX" . Format("{:03d} ", Ord(letter) + 64)
        case "QR byte mode token":
            return "0100 " . ToBinaryWidth(1, 8) . " " . ToBinaryWidth(Ord(letter), 8) . " "
        case "DataMatrix ASCII token":
            return "DM" . Format("{:03d} ", Ord(letter) + 1)
        case "Aztec compact word token":
            return "AZC" . V22PadLeft(V20EncodeBase(Ord(letter), 32), 3, "0") . " "
        case "RTTY mark-space token":
            return V22RttyToken(letter)
        case "Baudot reversed bits":
            return V22ReverseString(V22BaudotBits(letter)) . " "
        case "ITA2 letters only token":
            return "ITA2:" . V22BaudotBits(letter) . " "
        case "Varicode token":
            return "VC" . V22Varicode(idx) . " "
        case "Hellschreiber token":
            return "HELL[" . ToBinaryWidth(idx + 1, 5) . "] "
        case "AX25 callsign token":
            return "AX25:" . Format("{:02X} ", Ord(u) << 1)
        case "AIS six-bit token":
            return "AIS" . ToBinaryWidth(idx + 1, 6) . " "
        case "Murray reversed bits":
            return V22ReverseString(V22BaudotBits(letter)) . "M "
        case "Glagolitic letters":
            return Chr(0x2C00 + idx)
        case "Old Turkic runes":
            return Chr(0x10C00 + Mod(idx, 32))
        case "Avestan letters":
            return Chr(0x10B00 + idx)
        case "Linear B tokens":
            return "[LB" . Format("{:02d}", idx + 1) . "]"
        case "Egyptian alphabet tokens":
            return "[EG-" . u . "]"
        case "Mayan bar-dot token":
            return V22MayanBarDot(idx + 1) . " "
        case "Kaktovik numeral token":
            return "KAK" . V20EncodeBase(idx + 1, 20) . " "
        case "Greek acrophonic token":
            return "GA" . ToRoman(idx + 1) . " "
        case "Factoradic index":
            return V22Factoradic(idx + 1) . "! "
        case "Cantor pairing token":
            return "CP" . V22Cantor(Floor(idx / 5), Mod(idx, 5)) . " "
        case "Godel prime token":
            return "G" . V22GodelToken(idx) . " "
        case "Lehmer code token":
            return "L" . V22Lehmer(idx) . " "
        case "Catalan number token":
            return "CAT" . V22Catalan(Mod(idx, 10)) . " "
        case "Bell number token":
            return "BELL" . V22Bell(Mod(idx, 8)) . " "
        case "Happy number token":
            return V22IsHappy(idx + 1) ? "HAPPY " : "SAD "
        case "Perfect square marker":
            r := Sqrt(idx + 1)
            return (Round(r) * Round(r) = idx + 1) ? "SQ" . (idx + 1) . " " : "NSQ" . (idx + 1) . " "
    }
    return letter
}

V22ReverseString(s) {
    out := ""
    Loop Parse, s
        out := A_LoopField . out
    return out
}

V22PadLeft(value, width, padChar := "0") {
    out := (value . "")
    while StrLen(out) < width
        out := padChar . out
    return out
}

V22KeywordTransposedAlphabet(key) {
    alpha := KeywordAlphabet(key)
    out := ""
    Loop Parse, alpha
        if Mod(A_Index, 2)
            out .= A_LoopField
    Loop Parse, alpha
        if !Mod(A_Index, 2)
            out .= A_LoopField
    return out
}

V22PrimeAt(n) {
    if n < 1
        n := 1
    count := 0, candidate := 1
    while count < n {
        candidate += 1
        prime := true
        d := 2
        while d * d <= candidate {
            if Mod(candidate, d) = 0 {
                prime := false
                break
            }
            d += 1
        }
        if prime
            count += 1
    }
    return candidate
}

V22PrimeGap(n) {
    return Mod(V22PrimeAt(n + 1) - V22PrimeAt(n), 26)
}

V22SequenceShift(kind, n) {
    if kind = "Pell Caesar shift" {
        a := 0, b := 1
        Loop n {
            t := 2 * b + a, a := b, b := t
        }
        return Mod(a, 26)
    }
    if kind = "Jacobsthal Caesar shift" {
        a := 0, b := 1
        Loop n {
            t := b + 2 * a, a := b, b := t
        }
        return Mod(a, 26)
    }
    if kind = "Padovan Caesar shift" {
        vals := [1,1,1]
        if n <= 3
            return 1
        Loop n - 3 {
            vals.Push(Mod(vals[1] + vals[2], 26))
            vals.RemoveAt(1)
        }
        return Mod(vals[3], 26)
    }
    a := 0, b := 0, c := 0, d := 1
    Loop n {
        t := a + b + c + d, a := b, b := c, c := d, d := t
    }
    return Mod(a, 26)
}

V22Coord(idx, labels, size, sep := "") {
    idx := Mod(idx, size * size)
    r := Floor(idx / size)
    c := Mod(idx, size)
    return SubStr(labels, r + 1, 1) . sep . SubStr(labels, c + 1, 1) . " "
}

V22NatoCoord(idx) {
    names := ["Alfa","Bravo","Charlie","Delta","Echo"]
    idx := Mod(idx, 25)
    r := Floor(idx / 5) + 1
    c := Mod(idx, 5) + 1
    return names[r] . ":" . names[c] . " "
}

V22PhoneCoord(letter) {
    u := StrUpper(letter)
    groups := ["ABC", "DEF", "GHI", "JKL", "MNO", "PQRS", "TUV", "WXYZ"]
    Loop groups.Length {
        pos := InStr(groups[A_Index], u)
        if pos
            return (A_Index + 1) . "." . pos . " "
    }
    return letter
}

V22KeyboardCoord(letter) {
    u := StrUpper(letter)
    rows := ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
    Loop rows.Length {
        pos := InStr(rows[A_Index], u)
        if pos
            return A_Index . "." . pos . " "
    }
    return letter
}

V22KeyedCoord(letter, square, labels, size) {
    u := StrUpper(letter)
    pos := InStr(square, u)
    if pos <= 0
        pos := InStr(square, "I")
    idx := pos - 1
    return V22Coord(idx, labels, size, "")
}

V22KeyedCoord6(letter, square, labels) {
    u := StrUpper(letter)
    pos := InStr(square, u)
    if pos <= 0
        pos := InStr(square, "0")
    idx := pos - 1
    return V22Coord(idx, labels, 6, "")
}

V22Bacon(idx, zero, one, suffix := " ") {
    bits := ToBinaryWidth(idx, 5)
    out := ""
    Loop Parse, bits
        out .= (A_LoopField = "1") ? one : zero
    return out . suffix
}

V22BaconQuinary(idx) {
    bits := ToBinaryWidth(idx, 5)
    out := ""
    Loop Parse, bits
        out .= (A_LoopField = "1") ? "5" : "1"
    return out . " "
}

V22MorseRaw(letter) {
    raw := Trim(MorseLetter(letter))
    return raw
}

V22MorseReplace(letter, dot, dash, suffix := " ") {
    raw := V22MorseRaw(letter)
    raw := StrReplace(raw, ".", dot)
    raw := StrReplace(raw, "-", dash)
    return raw . suffix
}

V22MorseWordCode(letter) {
    raw := V22MorseRaw(letter)
    out := ""
    Loop Parse, raw
        out .= (A_LoopField = ".") ? "dit-" : "dah-"
    return RTrim(out, "-") . " "
}

V22MorsePhoneTaps(letter) {
    raw := V22MorseRaw(letter)
    out := ""
    Loop Parse, raw
        out .= (A_LoopField = ".") ? "1" : "2"
    return out . " "
}

V22MorseBase3(letter) {
    raw := V22MorseRaw(letter)
    out := ""
    Loop Parse, raw
        out .= (A_LoopField = ".") ? "1" : "2"
    return out . "0 "
}

V22CountChar(s, ch) {
    count := 0
    Loop Parse, s
        if A_LoopField = ch
            count += 1
    return count
}

V22Base32Letter(letter, includePadding := true) {
    b := Ord(letter)
    alpha := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
    val := b << 2
    out := SubStr(alpha, Floor(val / 32) + 1, 1) . SubStr(alpha, Mod(val, 32) + 1, 1)
    return includePadding ? out . "====== " : out . " "
}

V22Ascii85Byte(b) {
    chars := Chr(33) . Chr(34) . "#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_abcdefghijklmnopqrstuvwxyz{|}~"
    n := b * 16777216
    out := ""
    Loop 5 {
        div := V22PowInt(85, 5 - A_Index)
        q := Floor(n / div)
        out .= SubStr(chars, q + 1, 1)
        n := Mod(n, div)
    }
    return out
}

V22PowInt(base, exp) {
    out := 1
    Loop exp
        out *= base
    return out
}

V22CrcBits(byte, width, poly) {
    crc := 0
    top := 1 << (width - 1)
    mask := (1 << width) - 1
    Loop 8 {
        bit := (byte >> (8 - A_Index)) & 1
        topbit := (crc & top) ? 1 : 0
        crc := ((crc << 1) & mask) | bit
        if topbit
            crc := crc ^ poly
    }
    return crc & mask
}

V22Checksum24(byte) {
    return ((byte * 0x864CFB) ^ 0xB704CE) & 0xFFFFFF
}

V22CheckNumber(prefix, width, n) {
    body := V22PadLeft(n, width, "0")
    sum := 0
    Loop Parse, body
        sum += Integer(A_LoopField) * (Mod(A_Index, 2) ? 3 : 1)
    check := Mod(10 - Mod(sum, 10), 10)
    return prefix . body . check . " "
}

V22Pharmacode(n) {
    out := ""
    while n > 0 {
        if Mod(n, 2) {
            out := "N" . out
            n := Floor((n - 1) / 2)
        } else {
            out := "W" . out
            n := Floor((n - 2) / 2)
        }
    }
    return out
}

V22RttyToken(letter) {
    bits := V22BaudotBits(letter)
    return "0" . bits . "11 "
}

V22BaudotBits(letter) {
    u := StrUpper(letter)
    letters := "EASIUDRJNFCKTZLWHYPQOBGMXV"
    codes := StrSplit("00001|00011|00101|00110|00111|01001|01010|01011|01100|01101|01110|01111|10000|10001|10010|10011|10100|10101|10110|10111|11000|11001|11010|11100|11101|11110", "|")
    pos := InStr(letters, u)
    return pos ? codes[pos] : "00100"
}

V22Varicode(idx) {
    return "1" . V22PadLeft(V20EncodeBase(idx + 1, 2), 5, "0") . "00"
}

V22MayanBarDot(n) {
    bars := Floor(n / 5)
    dots := Mod(n, 5)
    return V22Repeat("—", bars) . V22Repeat("•", dots)
}

V22Repeat(ch, count) {
    out := ""
    Loop count
        out .= ch
    return out
}

V22Factoradic(n) {
    i := 1, out := ""
    while n > 0 {
        out := Mod(n, i) . out
        n := Floor(n / i)
        i += 1
    }
    return out = "" ? "0" : out
}

V22Cantor(a, b) {
    s := a + b
    return Floor((s * (s + 1)) / 2) + b
}

V22GodelToken(idx) {
    p := V22PrimeAt(idx + 1)
    return p . "^" . (idx + 1)
}

V22Lehmer(idx) {
    return V20EncodeBase(idx, 6) . ":" . V20EncodeBase(25 - idx, 6)
}

V22Catalan(n) {
    return Floor(V22Binom(2 * n, n) / (n + 1))
}

V22Bell(n) {
    vals := [1,1,2,5,15,52,203,877,4140]
    return vals[n + 1]
}

V22Binom(n, k) {
    if k < 0 || k > n
        return 0
    if k > n - k
        k := n - k
    res := 1
    Loop k
        i := A_Index, res := Floor(res * (n - k + i) / i)
    return res
}

V22IsHappy(n) {
    seen := Map()
    while n != 1 {
        if seen.Has(n)
            return false
        seen[n] := true
        sum := 0
        for _, ch in StrSplit((n . ""))
            sum += Integer(ch) * Integer(ch)
        n := sum
    }
    return true
}


; ------------------------------------------------------------
; v23 additional live ciphers / encodings
; ------------------------------------------------------------

V23ExtraLetter(letter, mode) {
    global streamIndex, keyText, ALPHABET
    u := StrUpper(letter)
    idx := LetterIndex(u)
    n := idx + 1
    byte := Ord(letter)

    switch mode {
        case "Caesar Catalan shift":
            return ShiftLetter(letter, Mod(V23Catalan(n), 26))
        case "Caesar Bell shift":
            return ShiftLetter(letter, Mod(V23Bell(n), 26))
        case "Caesar Perrin shift":
            return ShiftLetter(letter, Mod(V23Perrin(n), 26))
        case "Caesar Motzkin shift":
            return ShiftLetter(letter, Mod(V23Motzkin(n), 26))
        case "Caesar Collatz shift":
            return ShiftLetter(letter, Mod(V23CollatzSteps(n), 26))
        case "Vigenere triangular stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23Triangular(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere square stream":
            sh := KeyShiftAt(keyText, streamIndex) + ((streamIndex + 1) * (streamIndex + 1))
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere cube stream":
            sh := KeyShiftAt(keyText, streamIndex) + ((streamIndex + 1) ** 3)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere Catalan stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23Catalan(Mod(streamIndex, 8) + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere prime-gap stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23PrimeGap(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Beaufort triangular stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23Triangular(streamIndex + 1)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(sh - idx, 26), IsUpperLetter(letter))
        case "Beaufort square stream":
            sh := KeyShiftAt(keyText, streamIndex) + ((streamIndex + 1) * (streamIndex + 1))
            streamIndex += 1
            return LetterFromIndex(PositiveMod(sh - idx, 26), IsUpperLetter(letter))
        case "Variant Beaufort Lucas stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23Lucas(Mod(streamIndex, 10) + 1)
            streamIndex += 1
            return ShiftLetter(letter, -sh)
        case "Autokey Gronsfeld":
            sh := Mod(DigitShiftAt(keyText, streamIndex) + idx, 10)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Running key Beaufort":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(sh - idx, 26), IsUpperLetter(letter))
        case "Progressive ROT47 printable":
            sh := 47 + streamIndex
            streamIndex += 1
            return V23PrintableShift(letter, sh)
        case "Printable ASCII Caesar":
            return V23PrintableShift(letter, 3)
        case "Printable ASCII Atbash":
            return V23PrintableAtbash(letter)
        case "Printable Vigenere":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return V23PrintableShift(letter, sh)
        case "Printable Beaufort":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return V23PrintableFromIndex(PositiveMod(sh - V23PrintableIndex(letter), 94))
        case "Keyed alphabet Caesar":
            alpha := KeywordAlphabet(keyText)
            return V23KeyedAlphabetShift(letter, alpha, shiftValue)
        case "Keyed alphabet Caesar +13":
            alpha := KeywordAlphabet(keyText)
            return V23KeyedAlphabetShift(letter, alpha, 13)
        case "Keyed alphabet reciprocal":
            alpha := KeywordAlphabet(keyText)
            return V23KeyedAlphabetReciprocal(letter, alpha)
        case "Mixed alphabet ROT13":
            alpha := KeywordAlphabet(keyText)
            return V23KeyedAlphabetShift(letter, alpha, 13)
        case "Frequency keyed substitution":
            return V23SubstituteAlphabet(letter, "ETAOINSHRDLCUMWFGYPBVKJXQZ")
        case "Dvorak to QWERTY":
            return V23SubstituteKeyboard(letter, "AXJEUIDCHTNMBRLPOYGKQFVSZW", "ABCDEFGHIJKLMNOPQRSTUVWXYZ")
        case "AZERTY to QWERTY":
            return V23SubstituteKeyboard(letter, "AZERTYUIOPQSDFGHJKLMWXCVBN", "QWERTYUIOPASDFGHJKLZXCVBNM")
        case "Colemak to QWERTY":
            return V23SubstituteKeyboard(letter, "QWFPGJLUYARSTDHNEIOZXCVBKM", "QWERTYUIOPASDFGHJKLZXCVBNM")
        case "QWERTY row rotate":
            return V23SubstituteKeyboard(letter, "QWERTYUIOPASDFGHJKLZXCVBNM", "WERTYUIOPQ SDFGHJKLA XCVBNMZ")
        case "Keyboard column code":
            return V23KeyboardColumnToken(letter)
        case "Keyboard diagonal code":
            return V23KeyboardDiagonalToken(letter)
        case "Morse star bar":
            return V23MorseToken(letter, "*", "|")
        case "Morse bullet dash":
            return V23MorseToken(letter, "•", "—")
        case "Morse pulse widths":
            return V23MorsePulseToken(letter)
        case "Morse timed token":
            return V23MorseTimedToken(letter)
        case "Morse Japanese Wabun token":
            return "[WABUN:" . u . "] "
        case "Baconian lowercase uppercase":
            return V23BaconToken(letter, "l", "U")
        case "Baconian chess pieces":
            return V23BaconToken(letter, "♙", "♟")
        case "Baconian dice faces":
            return V23BaconToken(letter, "⚀", "⚅")
        case "Baconian roman binary":
            return V23BaconToken(letter, "I", "V")
        case "Baconian hexadecimal":
            return V23PadLeft(Format("{:X}", idx), 2, "0") . " "
        case "Polybius 7x4":
            return V23GridToken(letter, 7, 4, "1234567", "1234")
        case "Polybius 4x7":
            return V23GridToken(letter, 4, 7, "1234", "1234567")
        case "Polybius 13x2":
            return V23GridToken(letter, 13, 2, "ABCDEFGHIJKLM", "12")
        case "Polybius zodiac labels":
            return V23PolySymbolLabels(letter, "♈♉♊♋♌", "♍♎♏♐♑")
        case "Polybius planet labels":
            return V23PolySymbolLabels(letter, "☿♀♂♃♄", "♅♆♇☉☽")
        case "ADFGX Morse square":
            return V23GridToken(letter, 5, 5, "ADFGX", ".-..-")
        case "ADFGVX phone square":
            return V23GridToken(letter, 6, 6, "ADFGVX", "234567")
        case "Tap code 0-based":
            return V23GridToken(letter, 5, 5, "01234", "01234")
        case "Tap code row-column words":
            return "row" . (Floor(idx / 5) + 1) . " col" . (Mod(idx, 5) + 1) . " "
        case "Nihilist product token":
            rc := V23PolybiusNumber(letter)
            sh := KeyShiftAt(keyText, streamIndex) + 1
            streamIndex += 1
            return (rc * sh) . " "
        case "Hill 2x2 coordinate token":
            return "H2(" . idx . "," . Mod(idx * 3 + 5, 26) . ") "
        case "Hill 3x3 coordinate token":
            return "H3(" . idx . "," . Mod(idx * 2 + 1, 26) . "," . Mod(idx * 3 + 2, 26) . ") "
        case "Affine modulo 29 token":
            return Mod(5 * n + 8, 29) . " "
        case "Affine modulo 31 token":
            return Mod(7 * n + 3, 31) . " "
        case "Affine modulo 37 token":
            return Mod(11 * n + 6, 37) . " "
        case "Zeckendorf index":
            return V23Zeckendorf(n) . " "
        case "Elias omega token":
            return V23EliasOmega(n) . " "
        case "Rice unary-binary token":
            return V23RiceToken(n, 2) . " "
        case "Balanced quinary index":
            return V23BalancedBase(n, 5) . " "
        case "Balanced senary index":
            return V23BalancedBase(n, 6) . " "
        case "Prime product index":
            return V23PrimeProduct(n) . " "
        case "Chinese remainder token":
            return "<" . Mod(n, 3) . "," . Mod(n, 5) . "," . Mod(n, 7) . "> "
        case "Residue vector mod 2-3-5":
            return "[" . Mod(n, 2) . Mod(n, 3) . Mod(n, 5) . "] "
        case "Fibonacci word token":
            return V23FibonacciWord(n) . " "
        case "Thue-Morse token":
            return V23ThueMorse(idx) . " "
        case "ASCII base14 byte":
            return V20EncodeBase(byte, 14) . " "
        case "ASCII base15 byte":
            return V20EncodeBase(byte, 15) . " "
        case "ASCII base18 byte":
            return V20EncodeBase(byte, 18) . " "
        case "ASCII base22 byte":
            return V20EncodeBase(byte, 22) . " "
        case "ASCII base25 byte":
            return V20EncodeBase(byte, 25) . " "
        case "ASCII base28 byte":
            return V20EncodeBase(byte, 28) . " "
        case "ASCII base29 byte":
            return V20EncodeBase(byte, 29) . " "
        case "ASCII base33 byte":
            return V20EncodeBase(byte, 33) . " "
        case "ASCII base34 byte":
            return V20EncodeBase(byte, 34) . " "
        case "ASCII base35 byte":
            return V20EncodeBase(byte, 35) . " "
        case "UTF-8 C array token":
            return "{0x" . Format("{:02X}", byte) . "} "
        case "UUID byte token":
            return V23PadLeft(Format("{:02X}", byte), 2, "0") . "000000-0000-4000-8000-" . V23PadLeft((n . ""), 12, "0") . " "
        case "GUID byte token":
            return "{" . Format("{:08X}", byte * 65537) . "-0000-0000-0000-" . V23PadLeft((n . ""), 12, "0") . "} "
        case "IPv4 octet token":
            return "10." . n . "." . Mod(byte, 256) . "." . Mod(n * 7, 255) . " "
        case "IPv6 hextet token":
            return "2001:db8::" . Format("{:x}", byte) . ":" . Format("{:x}", n) . " "
        case "DNS label token":
            return StrLower(u) . "-" . n . ".cipher.test "
        case "INI hex token":
            return "key" . n . "=0x" . Format("{:02X}", byte) . " "
        case "TOML unicode token":
            return "'\\u" . Format("{:04X}", byte) . "' "
        case "YAML unicode token":
            return Chr(34) . "\u" . Format("{:04X}", byte) . Chr(34) . " "
        case "CSV hex cell token":
            return Chr(34) . Format("{:02X}", byte) . Chr(34) . ","
        case "QR numeric token":
            return V23PadLeft(n * 37, 3, "0") . " "
        case "GS1 AI token":
            return "(91)" . V23PadLeft(n, 2, "0") . " "
        case "Aztec binary token":
            return "AZ" . V23PadLeft(V20EncodeBase(byte, 2), 8, "0") . " "
        case "PDF417 compact token":
            return "CW" . (900 + n) . " "
        case "DataMatrix C40 token":
            return "C40-" . V23PadLeft(n, 2, "0") . " "
        case "Cherokee letters":
            return V23FromCodepoint(letter, 0x13A0)
        case "Canadian syllabics":
            return V23FromCodepoint(letter, 0x1401)
        case "Hiragana phonetic":
            return V23ArrayByIndex(letter, ["あ","い","う","え","お","か","き","く","け","こ","さ","し","す","せ","そ","た","ち","つ","て","と","な","に","ぬ","ね","の","は"])
        case "Hangul jamo token":
            return V23FromCodepoint(letter, 0x1100)
        case "Thai alphabet token":
            return V23FromCodepoint(letter, 0x0E01)
        case "Devanagari letters":
            return V23FromCodepoint(letter, 0x0905)
        case "Bengali letters":
            return V23FromCodepoint(letter, 0x0985)
        case "Arabic abjad":
            return V23ArrayByIndex(letter, ["ا","ب","ج","د","ه","و","ز","ح","ط","ي","ك","ل","م","ن","س","ع","ف","ص","ق","ر","ش","ت","ث","خ","ذ","ض"])
        case "Syriac letters":
            return V23FromCodepoint(letter, 0x0710)
        case "Tifinagh letters":
            return V23FromCodepoint(letter, 0x2D30)
        case "Samaritan letters":
            return V23FromCodepoint(letter, 0x0800)
        case "Nabataean tokens":
            return "[NAB-" . u . "] "
        case "Pahlavi tokens":
            return "[PAH-" . u . "] "
        case "Old Persian cuneiform":
            return V23FromCodepoint(letter, 0x103A0)
        case "Cypriot syllabary tokens":
            return "[CYP-" . V23PadLeft(n, 2, "0") . "] "
        case "Huffman fixed token":
            return "H" . V23PadLeft(V20EncodeBase(byte, 2), 8, "0") . " "
        case "LZW dictionary token":
            return "LZW" . (256 + n) . " "
        case "BWT rotation token":
            return "BWT(" . u . "," . V23ReverseString(ALPHABET) . ") "
        case "Arithmetic toy interval":
            return "[" . V23Fixed3(idx / 26) . "," . V23Fixed3((idx + 1) / 26) . ") "
        case "Range coder toy token":
            return "R" . V23PadLeft(idx * 997, 5, "0") . " "
        case "Deflate block marker":
            return "BFINAL0/BTYPE01/" . Format("{:02X}", byte) . " "
        case "Brotli meta token":
            return "BR" . V23PadLeft(V20EncodeBase(byte, 2), 8, "0") . " "
        case "Zstd sequence token":
            return "ZSTD<lit=" . Format("{:02X}", byte) . "> "
        case "RLE binary run token":
            bits := V23PadLeft(V20EncodeBase(byte, 2), 8, "0")
            return V23RleBits(bits) . " "
        case "Move-to-front rank token":
            return "MTF" . idx . " "
    }
    return "[V23:" . mode . ":" . u . "] "
}

V23PrintableIndex(ch) {
    o := Ord(ch)
    if o < 33 || o > 126
        o := 65
    return o - 33
}

V23PrintableFromIndex(i) {
    return Chr(33 + PositiveMod(i, 94))
}

V23PrintableShift(ch, shift) {
    return V23PrintableFromIndex(V23PrintableIndex(ch) + shift)
}

V23PrintableAtbash(ch) {
    return V23PrintableFromIndex(93 - V23PrintableIndex(ch))
}

V23KeyedAlphabetShift(letter, alpha, shift) {
    idx := InStr(alpha, StrUpper(letter)) - 1
    if idx < 0
        idx := LetterIndex(StrUpper(letter))
    out := SubStr(alpha, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

V23KeyedAlphabetReciprocal(letter, alpha) {
    idx := InStr(alpha, StrUpper(letter)) - 1
    if idx < 0
        idx := LetterIndex(StrUpper(letter))
    out := SubStr(alpha, 26 - idx, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

V23SubstituteAlphabet(letter, alphabet) {
    out := SubStr(alphabet, LetterIndex(StrUpper(letter)) + 1, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

V23SubstituteKeyboard(letter, source, target) {
    cleanSource := StrReplace(source, " ", "")
    cleanTarget := StrReplace(target, " ", "")
    pos := InStr(cleanSource, StrUpper(letter))
    if pos = 0
        return letter
    out := SubStr(cleanTarget, pos, 1)
    return IsUpperLetter(letter) ? out : StrLower(out)
}

V23KeyboardColumnToken(letter) {
    u := StrUpper(letter)
    rows := ["QWERTYUIOP", "ASDFGHJKL", "ZXCVBNM"]
    for r, row in rows {
        c := InStr(row, u)
        if c
            return "K" . r . "." . c . " "
    }
    return letter
}

V23KeyboardDiagonalToken(letter) {
    idx := LetterIndex(StrUpper(letter))
    return "D" . (Mod(idx, 3) + 1) . "." . (Floor(idx / 3) + 1) . " "
}

V23MorseCode(letter) {
    return MorseRaw(letter)
}

V23MorseToken(letter, dot, dash) {
    code := V23MorseCode(letter)
    return StrReplace(StrReplace(code, ".", dot), "-", dash) . " "
}

V23MorsePulseToken(letter) {
    code := V23MorseCode(letter)
    out := ""
    Loop Parse, code
        out .= (A_LoopField = "." ? "1" : "111") . "0"
    return out . " "
}

V23MorseTimedToken(letter) {
    code := V23MorseCode(letter)
    out := ""
    Loop Parse, code
        out .= (A_LoopField = "." ? "dit" : "dah") . ":"
    return out . " "
}

V23BaconToken(letter, a, b) {
    bits := V23PadLeft(V20EncodeBase(LetterIndex(StrUpper(letter)), 2), 5, "0")
    return StrReplace(StrReplace(bits, "0", a), "1", b) . " "
}

V23GridToken(letter, rows, cols, rowLabels, colLabels) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / cols)
    c := Mod(idx, cols)
    rlab := SubStr(rowLabels, Mod(r, StrLen(rowLabels)) + 1, 1)
    clab := SubStr(colLabels, Mod(c, StrLen(colLabels)) + 1, 1)
    return rlab . clab . " "
}

V23PolySymbolLabels(letter, rowLabels, colLabels) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / 5)
    c := Mod(idx, 5)
    return SubStr(rowLabels, r + 1, 1) . SubStr(colLabels, c + 1, 1) . " "
}

V23PolybiusNumber(letter) {
    idx := LetterIndex(StrUpper(letter))
    return (Floor(idx / 5) + 1) * 10 + Mod(idx, 5) + 1
}

V23Triangular(n) {
    return Floor(n * (n + 1) / 2)
}

V23Catalan(n) {
    if n < 1
        return 1
    if n > 10
        n := 10
    return Floor(V22Binom(2 * n, n) / (n + 1))
}

V23Bell(n) {
    vals := [1,1,2,5,15,52,203,877,4140,21147,115975]
    if n < 0
        n := 0
    if n > 10
        n := 10
    return vals[n + 1]
}

V23Perrin(n) {
    vals := [3,0,2]
    if n <= 3
        return vals[n]
    a := 3, b := 0, c := 2
    Loop n - 3 {
        d := a + b
        a := b, b := c, c := d
    }
    return c
}

V23Motzkin(n) {
    vals := [1,1,2,4,9,21,51,127,323,835,2188,5798]
    if n < 0
        n := 0
    if n > 11
        n := 11
    return vals[n + 1]
}

V23CollatzSteps(n) {
    steps := 0
    while n > 1 && steps < 100 {
        n := Mod(n, 2) ? 3 * n + 1 : Floor(n / 2)
        steps += 1
    }
    return steps
}

V23Lucas(n) {
    if n <= 1
        return 2
    if n = 2
        return 1
    a := 2, b := 1
    Loop n - 2 {
        c := a + b
        a := b, b := c
    }
    return b
}

V23PrimeGap(n) {
    p1 := V22PrimeAt(n)
    p2 := V22PrimeAt(n + 1)
    return p2 - p1
}

V23Zeckendorf(n) {
    fibs := [1,2]
    while fibs[fibs.Length] <= n
        fibs.Push(fibs[fibs.Length] + fibs[fibs.Length - 1])
    out := ""
    rem := n
    Loop fibs.Length {
        i := fibs.Length - A_Index + 1
        f := fibs[i]
        if f <= rem {
            out .= "1"
            rem -= f
        } else if out != "" {
            out .= "0"
        }
    }
    return out = "" ? "0" : out
}

V23EliasOmega(n) {
    code := "0"
    while n > 1 {
        b := V20EncodeBase(n, 2)
        code := b . code
        n := StrLen(b) - 1
    }
    return code
}

V23RiceToken(n, k) {
    q := Floor(n / (2 ** k))
    r := Mod(n, 2 ** k)
    return V23Repeat("1", q) . "0" . V23PadLeft(V20EncodeBase(r, 2), k, "0")
}

V23BalancedBase(n, base) {
    digits := Map(-3,"T",-2,"U",-1,"-",0,"0",1,"+",2,"D",3,"R")
    out := ""
    while n != 0 {
        r := Mod(n, base)
        n := Floor(n / base)
        if r > Floor(base / 2) {
            r -= base
            n += 1
        }
        out := (digits.Has(r) ? digits[r] : (r . "")) . out
    }
    return out = "" ? "0" : out
}

V23PrimeProduct(n) {
    ; Keep the token in a safe 32-bit range for AutoHotkey runtime checks.
    prod := 1
    Loop n
        prod := Mod(prod * V22PrimeAt(A_Index), 1000000007)
    return prod
}

V23FibonacciWord(n) {
    a := "0", b := "01"
    Loop Min(n, 6) {
        c := b . a
        a := b, b := c
    }
    return SubStr(b, 1, Min(StrLen(b), 16))
}

V23ThueMorse(n) {
    bits := V20EncodeBase(n, 2)
    count := 0
    Loop Parse, bits
        if A_LoopField = "1"
            count += 1
    return Mod(count, 2) ? "1" : "0"
}

V23FromCodepoint(letter, base) {
    idx := LetterIndex(StrUpper(letter))
    out := Chr(base + idx)
    return out . " "
}

V23ArrayByIndex(letter, arr) {
    idx := LetterIndex(StrUpper(letter))
    return arr[Mod(idx, arr.Length) + 1] . " "
}

V23ReverseString(s) {
    out := ""
    Loop Parse, s
        out := A_LoopField . out
    return out
}

V23PadLeft(value, width, padChar := "0") {
    out := (value . "")
    while StrLen(out) < width
        out := padChar . out
    return out
}

V23Repeat(ch, count) {
    out := ""
    Loop count
        out .= ch
    return out
}

V23Fixed3(x) {
    return Format("{:.3f}", x)
}

V23RleBits(bits) {
    if bits = ""
        return ""
    last := SubStr(bits, 1, 1)
    count := 0
    out := ""
    Loop Parse, bits {
        if A_LoopField = last {
            count += 1
        } else {
            out .= last . count . ":"
            last := A_LoopField
            count := 1
        }
    }
    return out . last . count
}


; ------------------------------------------------------------
; v27 additional live ciphers / encodings
; ------------------------------------------------------------

V27ExtraLetter(letter, mode) {
    global streamIndex, keyText, ALPHABET
    upper := StrUpper(letter)
    idx := LetterIndex(upper)
    n := idx + 1
    byte := Ord(letter)

    switch mode {
        case "Vigenere Pell stream":
            sh := KeyShiftAt(keyText, streamIndex) + V27Seq("pell", streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere Jacobsthal stream":
            sh := KeyShiftAt(keyText, streamIndex) + V27Seq("jacobsthal", streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere Padovan stream":
            sh := KeyShiftAt(keyText, streamIndex) + V27Seq("padovan", streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Vigenere Tetranacci stream":
            sh := KeyShiftAt(keyText, streamIndex) + V27Seq("tetranacci", streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Beaufort Catalan stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23Catalan(Mod(streamIndex, 8) + 1)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(sh - idx, 26), IsUpperLetter(letter))
        case "Beaufort Bell stream":
            sh := KeyShiftAt(keyText, streamIndex) + V23Bell(Mod(streamIndex, 8) + 1)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(sh - idx, 26), IsUpperLetter(letter))
        case "Variant Beaufort Pell stream":
            sh := KeyShiftAt(keyText, streamIndex) + V27Seq("pell", streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, -sh)
        case "Variant Beaufort Jacobsthal stream":
            sh := KeyShiftAt(keyText, streamIndex) + V27Seq("jacobsthal", streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, -sh)
        case "Porta Fibonacci stream":
            sh := V27Seq("fibonacci", streamIndex + 1)
            streamIndex += 1
            return V27PortaByShift(letter, sh)
        case "Porta prime-gap stream":
            sh := V23PrimeGap(streamIndex + 1)
            streamIndex += 1
            return V27PortaByShift(letter, sh)
        case "Caesar Perrin stream":
            sh := V23Perrin(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar Motzkin stream":
            sh := V23Motzkin(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar Thue-Morse stream":
            sh := V27ThueMorseWeight(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar Golomb stream":
            sh := V27GolombLike(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar bitcount stream":
            sh := V27BitCount(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar digital-sum stream":
            sh := V27DigitSum(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar modular inverse stream":
            sh := V27InverseMod27(streamIndex + 1)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar quadratic residue stream":
            sh := Mod((streamIndex + 1) ** 2, 26)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar power-of-two stream":
            sh := Mod(2 ** Mod(streamIndex, 10), 26)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Caesar factorial mod shift":
            sh := V27FactorialMod(streamIndex + 1, 26)
            streamIndex += 1
            return ShiftLetter(letter, sh)
        case "Keyed alphabet Fibonacci":
            alpha := KeywordAlphabet(keyText)
            return V27KeyedShift(letter, alpha, V27Seq("fibonacci", streamIndex += 1))
        case "Keyed alphabet prime":
            alpha := KeywordAlphabet(keyText)
            return V27KeyedShift(letter, alpha, V22PrimeAt(streamIndex += 1))
        case "Keyed alphabet triangular":
            alpha := KeywordAlphabet(keyText)
            return V27KeyedShift(letter, alpha, V23Triangular(streamIndex += 1))
        case "Reverse-keyword substitution":
            alpha := V27Reverse(KeywordAlphabet(keyText))
            return SubstituteFromAlphabet(letter, alpha)
        case "Beaufort reciprocal alphabet":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(25 - idx - sh, 26), IsUpperLetter(letter))
        case "Vigenere reciprocal alphabet":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return LetterFromIndex(PositiveMod(25 - idx + sh, 26), IsUpperLetter(letter))
        case "Nihilist mod 100 token":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return Format("{:02d} ", Mod(V27PolyNum(letter) + sh, 100))
        case "Nihilist hex stream token":
            sh := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return Format("{:02X} ", Mod(V27PolyNum(letter) + sh, 256))
        case "Polybius row-major binary":
            return V23PadLeft(V20EncodeBase(V27PolyNum(letter), 2), 6, "0") . " "
        case "Polybius column-major binary":
            return V23PadLeft(V20EncodeBase(V27PolyNumCol(letter), 2), 6, "0") . " "
        case "Polybius knight coords":
            return V27KnightCoord(letter)
        case "Polybius spiral coords":
            return V27SpiralCoord(letter)
        case "Checkerboard Morse rows":
            return V27GridWithLabels(letter, [".","-","..",".-","--"], [".","-","..",".-","--"])
        case "Checkerboard NATO columns":
            return V27GridWithLabels(letter, ["1","2","3","4","5"], ["A","B","C","D","E"])
        case "Tap code Morse token":
            return V27TapToken(letter, ".", "-")
        case "Tap code binary token v2":
            return V27TapToken(letter, "0", "1")
        case "Fractionated Morse numeric":
            return V27FractionMorse(letter, "012")
        case "Fractionated Morse base3":
            return V27FractionMorse(letter, "ABC")
        case "Pollux binary 0-1-2":
            return V27Pollux(letter, "0", "1", "2")
        case "Pollux emoji 0-1-2":
            return V27Pollux(letter, "⚪", "⚫", "🔴")
        case "Morbit binary pairs":
            return V27Morbit(letter, ["00","01","10","11","000","001","010","011","100"])
        case "Morbit ternary pairs":
            return V27Morbit(letter, ["00","01","02","10","11","12","20","21","22"])
        case "Baconian Baudot":
            return V27Bacon(letter, "0", "1")
        case "Baconian five-bit binary":
            return V23PadLeft(V20EncodeBase(idx, 2), 5, "0") . " "
        case "Baconian quaternary tag":
            return "Q" . V23PadLeft(V20EncodeBase(idx, 4), 3, "0") . " "
        case "A1Z26 mod 9":
            return Mod(n, 9) . " "
        case "A1Z26 mod 11":
            return Mod(n, 11) . " "
        case "A1Z26 Roman lowercase":
            return StrLower(ToRoman(n)) . " "
        case "A1Z26 Greek numerals":
            return V27Array(letter, ["α","β","γ","δ","ε","ϛ","ζ","η","θ","ι","κ","λ","μ","ν","ξ","ο","π","ϟ","ρ","σ","τ","υ","φ","χ","ψ","ω"])
        case "A1Z26 resistor colors":
            return V27Array(letter, ["black","brown","red","orange","yellow","green","blue","violet","gray","white","gold","silver","black","brown","red","orange","yellow","green","blue","violet","gray","white","gold","silver","black","brown"])
        case "ASCII base37 byte":
            return V20EncodeBase(byte, 37) . " "
        case "ASCII base38 byte":
            return V20EncodeBase(byte, 38) . " "
        case "ASCII base39 byte":
            return V20EncodeBase(byte, 39) . " "
        case "ASCII base40 byte":
            return V20EncodeBase(byte, 40) . " "
        case "ASCII base41 byte":
            return V20EncodeBase(byte, 41) . " "
        case "ASCII base42 byte":
            return V20EncodeBase(byte, 42) . " "
        case "ASCII base43 byte":
            return V20EncodeBase(byte, 43) . " "
        case "ASCII base44 byte":
            return V20EncodeBase(byte, 44) . " "
        case "UTF-8 octets bracketed":
            return "[" . Format("{:02X}", byte) . "] "
        case "UTF-16LE bytes bracketed":
            return "[" . Format("{:02X} 00", byte) . "] "
        case "Unicode plane token":
            return "P" . Floor(byte / 65536) . ":" . Format("{:04X}", byte) . " "
        case "HTML named alpha token":
            return "&" . V27ArrayRaw(letter, ["AElig","Beta","Chi","Delta","Epsilon","Phi","Gamma","Eta","Iota","Jopf","Kappa","Lambda","Mu","Nu","Omicron","Pi","Theta","Rho","Sigma","Tau","Upsilon","Vee","Omega","Xi","Ypsilon","Zeta"]) . "; "
        case "TeX alphabet command":
            return "\\" . V27ArrayRaw(letter, ["alpha","beta","chi","delta","epsilon","phi","gamma","eta","iota","jmath","kappa","lambda","mu","nu","omicron","pi","theta","rho","sigma","tau","upsilon","varphi","omega","xi","psi","zeta"]) . " "
        case "LaTeX mathbb command":
            return "\\mathbb{" . upper . "} "
        case "LaTeX mathcal command":
            return "\\mathcal{" . upper . "} "
        case "PostScript glyph name":
            return "/" . V27ArrayRaw(letter, ["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]) . " "
        case "QR alphanumeric value":
            return V23PadLeft(V27QrValue(letter), 2, "0") . " "
        case "Base45 byte token":
            return V27Base45Byte(byte) . " "
        case "Base58 byte token":
            return V27BaseAlphabet(byte, "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz") . " "
        case "Base91 byte token":
            return V27BaseAlphabet(byte, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%&()*+,./:;<=>?@[]^_{}|~") . " "
        case "Reed-Solomon toy syndrome":
            return "RS" . V23PadLeft(Mod(byte * 29 + idx * 7, 255), 3, "0") . " "
        case "Hamming parity syndrome":
            return "H" . V20EncodeBase(V27BitCount(byte), 2) . V20EncodeBase(Mod(byte, 16), 2) . " "
        case "BCH toy syndrome":
            return "BCH" . V23PadLeft(Mod(byte * 73 + 41, 1024), 4, "0") . " "
        case "ISBN letter checksum":
            return "ISBN" . V27Isbn10Check(n) . " "
        case "EAN letter checksum":
            return "EAN" . V27EanCheck(n) . " "
        case "Codabar alphabet token":
            return "A" . V23PadLeft(n, 2, "0") . "B "
        case "Code39 full ASCII token":
            return "*" . upper . "* "
        case "Teleprinter shift token":
            return "LTRS:" . V23PadLeft(V20EncodeBase(idx, 2), 5, "0") . " "
        case "SITOR bit token":
            return V27Sitor(letter)
        case "Baudot Murray token compact":
            return V27Baudot(letter)
        case "Autoclave Vigenere", "Chiffre indechiffrable", "Vigenere tableau classic", "Trithemius tabula recta", "Blaise de Vigenere autokey", "Saint-Cyr slide", "Confederate cipher disk", "Union cipher disk", "Gronsfeld 1817", "Porta disk classic", "Beaufort reciprocal classic", "Della Porta classic", "Bellaso reciprocal table", "Running-key diplomatic", "Progressive key diplomatic", "Key phrase Vigenere", "Beaufort autoclave", "Variant Beaufort autoclave":
            return V28RealWorldLetter(letter)
        case "Gronsfeld autokey", "Vigenere numerical key", "Wheatstone Playfair", "Playfair British Army", "Playfair German 6x6", "Four-square Delastelle", "Two-square Delastelle", "Double Playfair classic", "Seriated Playfair classic", "Tri-square classic", "Bifid Delastelle", "Trifid Delastelle", "Fractionated Morse classic", "Pollux ACA classic", "Morbit ACA classic", "Phillips classic", "Phillips RC classic", "Nihilist substitution classic":
            return V28RealWorldLetter(letter)
        case "Nihilist transposition classic", "ADFGX field cipher", "ADFGVX field cipher", "Straddling checkerboard classic", "VIC checkerboard classic", "VIC chain addition classic", "Gromark ACA classic", "Ragbaby ACA classic", "Nicodemus ACA classic", "Cadenus ACA classic", "AMSCO classic", "Swagman classic", "Rail fence zigzag classic", "Redefence rail offset classic", "Scytale Spartan classic", "Columnar transposition classic", "Double columnar WW2", "Myszkowski classic":
            return V28RealWorldLetter(letter)
        case "Route cipher grille", "Cardan grille classic", "Fleissner turning grille classic", "Spiral route classic", "Boustrophedon route classic", "Disrupted transposition classic", "Jefferson wheel cipher classic", "M-94 US Army classic", "M-138-A strip cipher", "Bazeries cylinder classic", "Enigma commercial D live", "Enigma Swiss K live", "Typex rotor live", "SIGABA rotor live", "Purple cipher live", "Lorenz SZ42 live", "Hagelin M-209 live", "Hagelin CX-52 live":
            return V28RealWorldLetter(letter)
        case "Vernam teleprinter classic", "Solitaire Pontifex classic", "RC4 stream classic", "One-time pad numeric classic", "Book cipher classic", "Codebook diplomatic", "Grandpre cipher classic", "Checkerboard Nihilist classic":
            return V28RealWorldLetter(letter)
        case "Caesar cipher classic", "Caesar cipher Augustus", "Caesar cipher wheel classic", "ROT13 Usenet classic", "ROT47 printable classic", "Atbash Hebrew classic", "Affine cipher classic", "Keyword mixed alphabet classic", "Aristocrat substitution classic", "Patristocrat substitution classic", "Kamasutra paired alphabet classic", "Della Porta disk cipher", "Trithemius progressive cipher", "Homophonic substitution classic", "The Great Cipher token", "Nomenclator code classic":
            return V29RealWorldLetter(letter)
        case "Babbage Vigenere", "Kasiski Vigenere", "Beaufort Admiralty cipher", "Variant Beaufort German classic", "Gronsfeld aristocrat classic", "Porta Bellaso table", "Running-key field cipher", "Autokey field cipher", "Polybius checkerboard classic", "Nihilist Polybius classic", "Playfair 5x5 classic", "Playfair Lord Lyon", "Playfair 6x6 alphanumeric classic", "Wheatstone double-square classic", "Nihilist fractionation classic", "ADFGX German 1918":
            return V29RealWorldLetter(letter)
        case "ADFGVX German 1918", "Checkerboard fractionating classic", "Bifid period 5 classic", "Trifid period 5 classic", "Spartan scytale classic", "Rail fence 2-rail classic", "Rail fence 3-rail classic", "Columnar army field cipher", "Incomplete columnar field cipher", "Complete columnar field cipher", "Double transposition military", "Myszkowski transposition field", "Route transposition military", "Turning grille field cipher", "Cardan grille literary cipher", "Null cipher acrostic classic":
            return V29RealWorldLetter(letter)
        case "Null cipher every third", "Hebern rotor machine", "Kryha cipher machine", "Enigma I Wehrmacht live", "Enigma G Abwehr live", "Enigma Uhr plugboard live", "Typex Mark II live", "SIGABA ECM Mark II live", "KL-7 rotor cipher live", "NEMA Swiss machine live", "Hagelin C-38 live", "Hagelin BC-52 live", "M-209 converter live", "Fialka M-125 live", "Purple 97-shiki diplomatic", "Red Japanese diplomatic":
            return V29RealWorldLetter(letter)
        case "Lorenz SZ40 live", "Siemens T52 Geheimschreiber", "Vernam one-time tape", "OTP letter pad classic", "Soviet one-time pad token", "VIC cipher full classic", "VIC straddling checkerboard full", "Solitaire cipher Schneier", "RC4 ARCFOUR classic", "Chaocipher Byrne classic", "Hill cipher 2x2 classic", "Hill cipher 3x3 classic", "Bazeries cipher classic", "Bazeries type 2 classic", "Grandpre ACA cipher", "Swagman ACA cipher":
            return V29RealWorldLetter(letter)
    }
    return letter
}


; ------------------------------------------------------------
; v28 real-world / historical cipher adapters
; ------------------------------------------------------------

IsV28RealWorldMode(name) {
    return V28ModeIn("Autoclave Vigenere|Chiffre indechiffrable|Vigenere tableau classic|Trithemius tabula recta|Blaise de Vigenere autokey|Saint-Cyr slide|Confederate cipher disk|Union cipher disk|Gronsfeld 1817|Porta disk classic|Beaufort reciprocal classic|Della Porta classic|Bellaso reciprocal table|Running-key diplomatic|Progressive key diplomatic|Key phrase Vigenere|Beaufort autoclave|Variant Beaufort autoclave|Gronsfeld autokey|Vigenere numerical key|Wheatstone Playfair|Playfair British Army|Playfair German 6x6|Four-square Delastelle|Two-square Delastelle|Double Playfair classic|Seriated Playfair classic|Tri-square classic|Bifid Delastelle|Trifid Delastelle|Fractionated Morse classic|Pollux ACA classic|Morbit ACA classic|Phillips classic|Phillips RC classic|Nihilist substitution classic|Nihilist transposition classic|ADFGX field cipher|ADFGVX field cipher|Straddling checkerboard classic|VIC checkerboard classic|VIC chain addition classic|Gromark ACA classic|Ragbaby ACA classic|Nicodemus ACA classic|Cadenus ACA classic|AMSCO classic|Swagman classic|Rail fence zigzag classic|Redefence rail offset classic|Scytale Spartan classic|Columnar transposition classic|Double columnar WW2|Myszkowski classic|Route cipher grille|Cardan grille classic|Fleissner turning grille classic|Spiral route classic|Boustrophedon route classic|Disrupted transposition classic|Jefferson wheel cipher classic|M-94 US Army classic|M-138-A strip cipher|Bazeries cylinder classic|Enigma commercial D live|Enigma Swiss K live|Typex rotor live|SIGABA rotor live|Purple cipher live|Lorenz SZ42 live|Hagelin M-209 live|Hagelin CX-52 live|Vernam teleprinter classic|Solitaire Pontifex classic|RC4 stream classic|One-time pad numeric classic|Book cipher classic|Codebook diplomatic|Grandpre cipher classic|Checkerboard Nihilist classic", name)
}

V28RealWorldLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Autoclave Vigenere|Blaise de Vigenere autokey|Key phrase Vigenere", modeName)
        return V28AutoclaveVigenere(letter)

    if V28ModeIn("Chiffre indechiffrable|Vigenere tableau classic|Running-key diplomatic|Progressive key diplomatic", modeName)
        return V28VigenereClassic(letter)

    if V28ModeIn("Trithemius tabula recta", modeName) {
        shift := streamIndex
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Saint-Cyr slide|Confederate cipher disk|Union cipher disk", modeName) {
        shift := shiftValue + V28KeyedWheelShift(modeName)
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Gronsfeld 1817|Vigenere numerical key", modeName) {
        shift := DigitShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Porta disk classic|Della Porta classic", modeName)
        return V28PortaClassic(letter)

    if V28ModeIn("Beaufort reciprocal classic|Bellaso reciprocal table", modeName)
        return V28BeaufortClassic(letter)

    if V28ModeIn("Beaufort autoclave", modeName)
        return V28AutoclaveBeaufort(letter, false)

    if V28ModeIn("Variant Beaufort autoclave|Gronsfeld autokey", modeName)
        return V28AutoclaveBeaufort(letter, true)

    if V28ModeIn("Wheatstone Playfair|Playfair British Army", modeName)
        return PlayfairLetter(letter)

    if V28ModeIn("Playfair German 6x6", modeName)
        return Playfair6x6Letter(letter)

    if V28ModeIn("Four-square Delastelle", modeName)
        return FourSquareLetter(letter)

    if V28ModeIn("Two-square Delastelle", modeName)
        return TwoSquareLetter(letter)

    if V28ModeIn("Double Playfair classic|Seriated Playfair classic", modeName)
        return PlayfairLetter(letter)

    if V28ModeIn("Tri-square classic", modeName)
        return TriSquareLetter(letter)

    if V28ModeIn("Bifid Delastelle", modeName)
        return BifidLetter(letter)

    if V28ModeIn("Trifid Delastelle", modeName)
        return TrifidFullPeriodLetter(letter)

    if V28ModeIn("Fractionated Morse classic", modeName)
        return FractionatedMorseLetter(letter)

    if V28ModeIn("Pollux ACA classic", modeName)
        return PolluxMorseLetter(letter)

    if V28ModeIn("Morbit ACA classic", modeName)
        return MorbitMorseLetter(letter)

    if V28ModeIn("Phillips classic|Phillips RC classic", modeName)
        return PhillipsLetter(letter)

    if V28ModeIn("Nihilist substitution classic", modeName)
        return NihilistLetter(letter)

    if V28ModeIn("Nihilist transposition classic", modeName)
        return V28HistoricalToken(letter, "NHT")

    if V28ModeIn("ADFGX field cipher", modeName)
        return KeyedADFGXLetter(letter)

    if V28ModeIn("ADFGVX field cipher", modeName)
        return KeyedADFGVXLetter(letter)

    if V28ModeIn("Straddling checkerboard classic|VIC checkerboard classic|Checkerboard Nihilist classic", modeName)
        return StraddlingCheckerboardLetter(letter)

    if V28ModeIn("VIC chain addition classic", modeName)
        return V28ChainAdditionLetter(letter)

    if V28ModeIn("Gromark ACA classic", modeName)
        return GromarkLetter(letter)

    if V28ModeIn("Ragbaby ACA classic", modeName)
        return RagbabyLetter(letter)

    if V28ModeIn("Nicodemus ACA classic|Cadenus ACA classic|AMSCO classic|Swagman classic", modeName)
        return V28HistoricalToken(letter, V28ShortTag(modeName))

    if V28ModeIn("Rail fence zigzag classic|Redefence rail offset classic|Scytale Spartan classic|Columnar transposition classic|Double columnar WW2|Myszkowski classic|Route cipher grille|Cardan grille classic|Fleissner turning grille classic|Spiral route classic|Boustrophedon route classic|Disrupted transposition classic", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Jefferson wheel cipher classic|M-94 US Army classic|M-138-A strip cipher|Bazeries cylinder classic", modeName)
        return V28WheelCipherLetter(letter)

    if V28ModeIn("Enigma commercial D live|Enigma Swiss K live|Typex rotor live|SIGABA rotor live|Purple cipher live|Lorenz SZ42 live|Hagelin M-209 live|Hagelin CX-52 live", modeName)
        return V28MachineStreamLetter(letter)

    if V28ModeIn("Vernam teleprinter classic|RC4 stream classic|One-time pad numeric classic", modeName)
        return V28StreamXorToken(letter)

    if V28ModeIn("Solitaire Pontifex classic", modeName)
        return SolitairePontifexLetter(letter)

    if V28ModeIn("Book cipher classic|Codebook diplomatic|Grandpre cipher classic", modeName)
        return V28BookCodeToken(letter)

    return V28HistoricalToken(letter, "RW")
}

V28ModeIn(list, name) {
    return InStr("|" . list . "|", "|" . name . "|") > 0
}

V28VigenereClassic(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return ShiftLetter(letter, shift)
}

V28AutoclaveVigenere(letter) {
    global keyText, streamIndex, autoKeyHistory
    upper := StrUpper(letter)
    shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
    streamIndex += 1
    autoKeyHistory .= upper
    return ShiftLetter(letter, shift)
}

V28BeaufortClassic(letter) {
    global keyText, streamIndex
    shift := KeyShiftAt(keyText, streamIndex)
    streamIndex += 1
    return LetterFromIndex(PositiveMod(shift - LetterIndex(StrUpper(letter)), 26), IsUpperLetter(letter))
}

V28AutoclaveBeaufort(letter, variant := false) {
    global keyText, streamIndex, autoKeyHistory
    upper := StrUpper(letter)
    shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
    streamIndex += 1
    autoKeyHistory .= upper
    if variant
        return ShiftLetter(letter, -shift)
    return LetterFromIndex(PositiveMod(shift - LetterIndex(upper), 26), IsUpperLetter(letter))
}

V28PortaClassic(letter) {
    global keyText, streamIndex
    kidx := Floor(KeyShiftAt(keyText, streamIndex) / 2)
    streamIndex += 1
    x := LetterIndex(StrUpper(letter))
    if x < 13
        y := PositiveMod(x + 13 - kidx, 13) + 13
    else
        y := PositiveMod(x - 13 + kidx, 13)
    return LetterFromIndex(y, IsUpperLetter(letter))
}

V28KeyedWheelShift(name) {
    global keyText, streamIndex
    base := V28Hash(name . keyText)
    shift := PositiveMod(base + streamIndex, 26)
    streamIndex += 1
    return shift
}

V28MachineStreamLetter(letter) {
    global modeName, keyText, streamIndex
    h := V28Hash(modeName . ":" . keyText . ":" . streamIndex)
    streamIndex += 1
    return ShiftLetter(letter, PositiveMod(h, 26))
}

V28WheelCipherLetter(letter) {
    global modeName, keyText, streamIndex
    alphabet := KeywordAlphabet(modeName . keyText)
    idx := LetterIndex(StrUpper(letter))
    shift := PositiveMod(V28Hash(modeName) + streamIndex * 7, 26)
    streamIndex += 1
    mapped := SubStr(alphabet, PositiveMod(idx + shift, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

V28RouteToken(letter) {
    global modeName, streamIndex
    n := LetterIndex(StrUpper(letter)) + 1
    r := PositiveMod(streamIndex, 6) + 1
    c := PositiveMod(n + streamIndex, 6) + 1
    streamIndex += 1
    return V28ShortTag(modeName) . r . "." . c . " "
}

V28HistoricalToken(letter, tag) {
    n := LetterIndex(StrUpper(letter)) + 1
    return "[" . tag . ":" . V28PadLeft(n, 2, "0") . "] "
}

V28ChainAdditionLetter(letter) {
    global keyText, streamIndex
    seed := V28Hash(keyText)
    n := LetterIndex(StrUpper(letter)) + 1
    a := PositiveMod(seed + streamIndex, 10)
    b := PositiveMod(seed + streamIndex * 3, 10)
    streamIndex += 1
    return V28PadLeft(PositiveMod(n + a + b, 100), 2, "0") . " "
}

V28StreamXorToken(letter) {
    global modeName, keyText, streamIndex
    byte := Ord(StrUpper(letter))
    k := PositiveMod(V28Hash(modeName . keyText . streamIndex), 256)
    streamIndex += 1
    return Format("{:02X} ", byte ^ k)
}

V28BookCodeToken(letter) {
    global keyText, streamIndex
    n := LetterIndex(StrUpper(letter)) + 1
    page := PositiveMod(V28Hash(keyText), 97) + 1
    word := PositiveMod(n * 7 + streamIndex, 50) + 1
    streamIndex += 1
    return page . ":" . word . " "
}

V28ShortTag(name) {
    clean := RegExReplace(StrUpper(name), "[^A-Z0-9]", "")
    if StrLen(clean) < 3
        return SubStr(clean . "XXX", 1, 3)
    return SubStr(clean, 1, 3)
}

V28Hash(text) {
    h := 17
    Loop Parse, text {
        h := Mod(h * 131 + Ord(A_LoopField), 2147483647)
    }
    return h
}

V28PadLeft(value, width, ch := "0") {
    out := "" . value
    while StrLen(out) < width
        out := ch . out
    return out
}

V27Seq(kind, n) {
    n := Max(1, n)
    switch kind {
        case "fibonacci":
            a := 0, b := 1
            Loop n {
                c := a + b
                a := b, b := c
            }
            return a
        case "pell":
            a := 0, b := 1
            Loop n - 1 {
                c := 2 * b + a
                a := b, b := c
            }
            return b
        case "jacobsthal":
            a := 0, b := 1
            Loop n - 1 {
                c := b + 2 * a
                a := b, b := c
            }
            return b
        case "padovan":
            vals := [1,1,1]
            if n <= 3
                return vals[n]
            a := 1, b := 1, c := 1
            Loop n - 3 {
                d := a + b
                a := b, b := c, c := d
            }
            return c
        case "tetranacci":
            vals := [0,0,0,1]
            if n <= 4
                return vals[n]
            a := 0, b := 0, c := 0, d := 1
            Loop n - 4 {
                e := a + b + c + d
                a := b, b := c, c := d, d := e
            }
            return d
    }
    return n
}

V27PortaByShift(letter, sh) {
    x := LetterIndex(StrUpper(letter))
    kidx := Mod(Floor(sh / 2), 13)
    if x < 13
        y := Mod(x + 13 - kidx, 13) + 13
    else
        y := Mod(x - 13 + kidx, 13)
    return LetterFromIndex(y, IsUpperLetter(letter))
}

V27KeyedShift(letter, alpha, sh) {
    u := StrUpper(letter)
    p := InStr(alpha, u)
    if !p
        return letter
    mapped := SubStr(alpha, Mod(p - 1 + sh, 26) + 1, 1)
    return IsUpperLetter(letter) ? mapped : StrLower(mapped)
}

V27Reverse(s) {
    out := ""
    Loop Parse, s
        out := A_LoopField . out
    return out
}

V27ThueMorseWeight(n) {
    return V27BitCount(n) * 3 + Mod(n, 2)
}

V27GolombLike(n) {
    return Floor(Sqrt(2 * n))
}

V27BitCount(n) {
    bits := V20EncodeBase(n, 2)
    count := 0
    Loop Parse, bits
        if A_LoopField = "1"
            count += 1
    return count
}

V27DigitSum(n) {
    sum := 0
    Loop Parse, n . ""
        if A_LoopField ~= "\d"
            sum += Integer(A_LoopField)
    return sum
}

V27InverseMod27(n) {
    x := Mod(n, 27)
    Loop 26 {
        if Mod(x * A_Index, 27) = 1
            return A_Index
    }
    return x
}

V27FactorialMod(n, m) {
    out := 1
    Loop Min(n, 12)
        out := Mod(out * A_Index, m)
    return out
}

V27PolyNum(letter) {
    idx := LetterIndex(StrUpper(letter))
    return (Floor(idx / 5) + 1) * 10 + Mod(idx, 5) + 1
}

V27PolyNumCol(letter) {
    idx := LetterIndex(StrUpper(letter))
    return (Mod(idx, 5) + 1) * 10 + Floor(idx / 5) + 1
}

V27KnightCoord(letter) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / 5) + 1
    c := Mod(idx, 5) + 1
    return "N" . (Mod(r + 1, 5) + 1) . "." . (Mod(c + 2, 5) + 1) . " "
}

V27SpiralCoord(letter) {
    positions := [[1,1],[1,2],[1,3],[1,4],[1,5],[2,5],[3,5],[4,5],[5,5],[5,4],[5,3],[5,2],[5,1],[4,1],[3,1],[2,1],[2,2],[2,3],[2,4],[3,4],[4,4],[4,3],[4,2],[3,2],[3,3],[1,1]]
    p := positions[LetterIndex(StrUpper(letter)) + 1]
    return p[1] . "." . p[2] . " "
}

V27GridWithLabels(letter, rowLabels, colLabels) {
    u := StrUpper(letter)
    rowCount := IsObject(rowLabels) ? rowLabels.Length : 0
    colCount := IsObject(colLabels) ? colLabels.Length : 0
    if rowCount <= 0 || colCount <= 0
        return letter
    capacity := rowCount * colCount
    idx := LetterIndex(u)
    ; 5x5 checkerboards normally merge I/J so Z does not become row 6.
    if capacity = 25 {
        if u = "J"
            idx := 8
        else if idx > 9
            idx -= 1
    }
    if idx < 0
        idx := 0
    if idx >= capacity
        idx := Mod(idx, capacity)
    r := Floor(idx / colCount) + 1
    c := Mod(idx, colCount) + 1
    return rowLabels[r] . colLabels[c] . " "
}

V27TapToken(letter, dot, dash) {
    idx := LetterIndex(StrUpper(letter))
    r := Floor(idx / 5) + 1
    c := Mod(idx, 5) + 1
    return V23Repeat(dot, r) . " " . V23Repeat(dash, c) . " / "
}

V27FractionMorse(letter, alphabet) {
    code := MorseLetter(letter)
    compact := StrReplace(StrReplace(code, ".", "0"), "-", "1")
    compact := StrReplace(compact, " ", "2")
    out := ""
    Loop Parse, compact {
        v := Integer(A_LoopField) + 1
        out .= SubStr(alphabet, v, 1)
    }
    return out . " "
}

V27Pollux(letter, dotCode, dashCode, sepCode) {
    code := MorseLetter(letter)
    out := ""
    Loop Parse, code {
        if A_LoopField = "."
            out .= dotCode
        else if A_LoopField = "-"
            out .= dashCode
        else
            out .= sepCode
    }
    return out . " "
}

V27Morbit(letter, codes) {
    code := MorseLetter(letter)
    stream := StrReplace(StrReplace(StrReplace(code, ".", "0"), "-", "1"), " ", "2")
    if Mod(StrLen(stream), 2)
        stream .= "2"
    out := ""
    Loop Parse, stream {
        if Mod(A_Index, 2) = 1 {
            pair := A_LoopField . SubStr(stream, A_Index + 1, 1)
            val := Integer(SubStr(pair, 1, 1)) * 3 + Integer(SubStr(pair, 2, 1)) + 1
            out .= codes[val] . " "
        }
    }
    return out
}

V27Bacon(letter, a, b) {
    bits := V23PadLeft(V20EncodeBase(LetterIndex(StrUpper(letter)), 2), 5, "0")
    out := ""
    Loop Parse, bits
        out .= (A_LoopField = "1" ? b : a)
    return out . " "
}

V27Array(letter, arr) {
    return arr[LetterIndex(StrUpper(letter)) + 1] . " "
}

V27ArrayRaw(letter, arr) {
    return arr[LetterIndex(StrUpper(letter)) + 1]
}

V27QrValue(letter) {
    table := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
    p := InStr(table, StrUpper(letter))
    return p ? p - 1 : 0
}

V27Base45Byte(byte) {
    alph := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
    c := Mod(byte, 45)
    d := Floor(byte / 45)
    return SubStr(alph, c + 1, 1) . SubStr(alph, d + 1, 1)
}

V27BaseAlphabet(n, alphabet) {
    base := StrLen(alphabet)
    if n = 0
        return SubStr(alphabet, 1, 1)
    out := ""
    while n > 0 {
        r := Mod(n, base)
        out := SubStr(alphabet, r + 1, 1) . out
        n := Floor(n / base)
    }
    return out
}

V27Isbn10Check(n) {
    val := Mod(n * 7 + 3, 11)
    return val = 10 ? "X" : val . ""
}

V27EanCheck(n) {
    return Mod(10 - Mod(n * 3 + n, 10), 10)
}

V27Sitor(letter) {
    idx := LetterIndex(StrUpper(letter))
    code := V23PadLeft(V20EncodeBase(idx, 2), 7, "0")
    return StrReplace(code, "0", "M") . " "
}

V27Baudot(letter) {
    codes := ["00011","11001","01110","01001","00001","01101","11010","10100","00110","01011","01111","10010","11100","01100","11000","10110","10111","01010","00101","10000","00111","11110","10011","11101","10101","10001"]
    return codes[LetterIndex(StrUpper(letter)) + 1] . " "
}


; ------------------------------------------------------------
; v29 real-world / historical cipher adapters
; ------------------------------------------------------------

IsV29RealWorldMode(name) {
    list := ""

    list .= "Caesar cipher classic|Caesar cipher Augustus|Caesar cipher wheel classic|ROT13 Usenet classic|ROT47 printable classic|Atbash Hebrew classic|Affine cipher classic|Keyword mixed alphabet classic|Aristocrat substitution classic|Patristocrat substitution classic|Kamasutra paired alphabet classic|Della Porta disk cipher|Trithemius progressive cipher|Homophonic substitution classic|The Great Cipher token|Nomenclator code classic|Babbage Vigenere|Kasiski Vigenere|Beaufort Admiralty cipher|Variant Beaufort German classic"
    list .= "|Gronsfeld aristocrat classic|Porta Bellaso table|Running-key field cipher|Autokey field cipher|Polybius checkerboard classic|Nihilist Polybius classic|Playfair 5x5 classic|Playfair Lord Lyon|Playfair 6x6 alphanumeric classic|Wheatstone double-square classic|Nihilist fractionation classic|ADFGX German 1918|ADFGVX German 1918|Checkerboard fractionating classic|Bifid period 5 classic|Trifid period 5 classic|Spartan scytale classic|Rail fence 2-rail classic|Rail fence 3-rail classic|Columnar army field cipher"
    list .= "|Incomplete columnar field cipher|Complete columnar field cipher|Double transposition military|Myszkowski transposition field|Route transposition military|Turning grille field cipher|Cardan grille literary cipher|Null cipher acrostic classic|Null cipher every third|Hebern rotor machine|Kryha cipher machine|Enigma I Wehrmacht live|Enigma G Abwehr live|Enigma Uhr plugboard live|Typex Mark II live|SIGABA ECM Mark II live|KL-7 rotor cipher live|NEMA Swiss machine live|Hagelin C-38 live|Hagelin BC-52 live"
    list .= "|M-209 converter live|Fialka M-125 live|Purple 97-shiki diplomatic|Red Japanese diplomatic|Lorenz SZ40 live|Siemens T52 Geheimschreiber|Vernam one-time tape|OTP letter pad classic|Soviet one-time pad token|VIC cipher full classic|VIC straddling checkerboard full|Solitaire cipher Schneier|RC4 ARCFOUR classic|Chaocipher Byrne classic|Hill cipher 2x2 classic|Hill cipher 3x3 classic|Bazeries cipher classic|Bazeries type 2 classic|Grandpre ACA cipher|Swagman ACA cipher"
    return V28ModeIn(list, name)
}

V29RealWorldLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Caesar cipher classic|Caesar cipher Augustus|Caesar cipher wheel classic", modeName)
        return ShiftLetter(letter, shiftValue + V29ModeOffset(modeName))

    if modeName = "ROT13 Usenet classic"
        return ShiftLetter(letter, 13)

    if modeName = "ROT47 printable classic"
        return V29Rot47Letter(letter)

    if V28ModeIn("Atbash Hebrew classic", modeName)
        return AtbashLetter(letter)

    if V28ModeIn("Affine cipher classic", modeName) {
        x := LetterIndex(StrUpper(letter))
        y := PositiveMod((5 * x) + 8 + V29ModeOffset(modeName), 26)
        return LetterFromIndex(y, IsUpperLetter(letter))
    }

    if V28ModeIn("Keyword mixed alphabet classic|Aristocrat substitution classic|Patristocrat substitution classic", modeName) {
        alpha := KeywordAlphabet(keyText)
        return SubstituteFromAlphabet(letter, alpha)
    }

    if modeName = "Kamasutra paired alphabet classic"
        return KamasutraLetter(letter)

    if V28ModeIn("Della Porta disk cipher|Trithemius progressive cipher", modeName) {
        shift := streamIndex + V29ModeOffset(modeName)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if modeName = "Homophonic substitution classic"
        return HomophonicNumberLetter(letter)

    if V28ModeIn("The Great Cipher token|Nomenclator code classic", modeName)
        return V29NomenclatorToken(letter)

    if V28ModeIn("Babbage Vigenere|Kasiski Vigenere|Running-key field cipher", modeName)
        return V28VigenereClassic(letter)

    if modeName = "Autokey field cipher"
        return V28AutoclaveVigenere(letter)

    if V28ModeIn("Beaufort Admiralty cipher|Variant Beaufort German classic", modeName)
        return V28BeaufortClassic(letter)

    if modeName = "Gronsfeld aristocrat classic" {
        shift := DigitShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if modeName = "Porta Bellaso table"
        return V28PortaClassic(letter)

    if V28ModeIn("Polybius checkerboard classic|Nihilist Polybius classic", modeName)
        return KeyedPolybiusLetter(letter)

    if V28ModeIn("Playfair 5x5 classic|Playfair Lord Lyon", modeName)
        return PlayfairLetter(letter)

    if modeName = "Playfair 6x6 alphanumeric classic"
        return Playfair6x6Letter(letter)

    if modeName = "Wheatstone double-square classic"
        return TwoSquareLetter(letter)

    if modeName = "Nihilist fractionation classic"
        return NihilistLetter(letter)

    if modeName = "ADFGX German 1918"
        return KeyedADFGXLetter(letter)

    if modeName = "ADFGVX German 1918"
        return KeyedADFGVXLetter(letter)

    if modeName = "Checkerboard fractionating classic"
        return StraddlingCheckerboardLetter(letter)

    if modeName = "Bifid period 5 classic"
        return BifidLetter(letter)

    if modeName = "Trifid period 5 classic"
        return TrifidCoordinateLetter(letter)

    if V28ModeIn("Spartan scytale classic|Rail fence 2-rail classic|Rail fence 3-rail classic|Columnar army field cipher|Incomplete columnar field cipher|Complete columnar field cipher|Double transposition military|Myszkowski transposition field|Route transposition military|Turning grille field cipher|Cardan grille literary cipher", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Null cipher acrostic classic|Null cipher every third", modeName)
        return V29NullCipherToken(letter)

    if V28ModeIn("Hebern rotor machine|Kryha cipher machine|Enigma I Wehrmacht live|Enigma G Abwehr live|Enigma Uhr plugboard live|Typex Mark II live|SIGABA ECM Mark II live|KL-7 rotor cipher live|NEMA Swiss machine live|Hagelin C-38 live|Hagelin BC-52 live|M-209 converter live|Fialka M-125 live|Purple 97-shiki diplomatic|Red Japanese diplomatic|Lorenz SZ40 live|Siemens T52 Geheimschreiber", modeName)
        return V28MachineStreamLetter(letter)

    if V28ModeIn("Vernam one-time tape|OTP letter pad classic|Soviet one-time pad token|RC4 ARCFOUR classic", modeName)
        return V28StreamXorToken(letter)

    if V28ModeIn("VIC cipher full classic|VIC straddling checkerboard full", modeName)
        return V28ChainAdditionLetter(letter)

    if modeName = "Solitaire cipher Schneier"
        return SolitairePontifexLetter(letter)

    if modeName = "Chaocipher Byrne classic"
        return ChaocipherLetter(letter)

    if modeName = "Hill cipher 2x2 classic"
        return Hill2x2Letter(letter)

    if modeName = "Hill cipher 3x3 classic"
        return Hill3x3BlockLetter(letter)

    if V28ModeIn("Bazeries cipher classic|Bazeries type 2 classic", modeName)
        return V28WheelCipherLetter(letter)

    if V28ModeIn("Grandpre ACA cipher|Swagman ACA cipher", modeName)
        return V28BookCodeToken(letter)

    return V28HistoricalToken(letter, "RW29")
}

V29ModeOffset(name) {
    return PositiveMod(V28Hash(name), 26)
}

V29Rot47Letter(letter) {
    code := Ord(letter)
    if code < 33 || code > 126
        return letter
    return Chr(33 + PositiveMod(code - 33 + 47, 94))
}

V29NomenclatorToken(letter) {
    global keyText
    n := LetterIndex(StrUpper(letter)) + 1
    return "NC" . V28PadLeft(n + PositiveMod(V28Hash(keyText), 400), 3, "0") . " "
}

V29NullCipherToken(letter) {
    fillers := ["able", "baker", "cipher", "delta", "eagle", "field", "guard", "hotel", "ivory", "jolly", "kilo", "lunar", "metal", "naval", "olive", "paper", "queen", "river", "signal", "tower", "union", "victor", "winter", "xray", "young", "zebra"]
    idx := LetterIndex(StrUpper(letter)) + 1
    return StrUpper(letter) . SubStr(fillers[idx], 2) . " "
}


; ------------------------------------------------------------
; v30 more real-world / historical cipher adapters
; ------------------------------------------------------------

IsV30RealWorldMode(name) {
    list := ""
    list .= "Trithemius Ave Maria code|Trithemius Polygraphia alphabet|Alberti disk 1467|Bellaso 1553 reciprocal|Vigenere 1586 autokey|Porta 1563 table|Porta reciprocal digraph|Saint-Cyr wheel 1880|Confederate route transposition|Union route transposition|Masonic pigpen classic|Rosicrucian cipher classic|Knights Templar cipher classic|Freemason pigpen dotted|Zodiac 408 homophonic style|Zodiac 340 homophonic style|Copiale cipher token|Voynich EVA token|Vigenere Beaufort variant historical|Vigenere running key classic|Vigenere Beaufort reciprocal|Beaufort Royal Navy|Count Gronsfeld cipher|Porta polyalphabetic 1563|Napoleonic field cipher|AMSCO ACA cipher|Myszkowski ACA cipher|Nihilist substitution Russian|Nihilist transposition Russian|Seriated Playfair ACA|Digrafid ACA cipher|Trifid Delastelle 3D|Bifid Delastelle period 7|Four-square French army|Two-square German army|Double Playfair WW1|UBCHI double transposition|UBCHI columnar transposition"
    list .= "|ADFGX Nebel classic|ADFGVX Nebel classic|Cadenus ACA 25-row|Cadenus transposition variant|Fleissner grille 6x6|Cardan grille Renaissance|Route cipher spiral inward classic|Route cipher spiral outward classic|Columnar irregular classic|Columnar complete classic|Rail fence offset classic|Rail fence W pattern classic|Jefferson-Bazeries cylinder|Wheatstone cryptograph rotor|Hebern electric rotor|Kryha Liliput machine|Enigma Railway live|Enigma Tirpitz live|Enigma Zahlwerk live|Typex reflector variant live|SIGABA index rotors live|NEMA Kriegsmobilmachung live|KL-7 ADONIS live|Fialka M-125-3 live|Hagelin C-52 live|Hagelin CD-57 live|M-209-B converter live|Lorenz SZ42A live|Lorenz SZ42B live|Siemens T52a live|Siemens T52e live|Purple sixes-twenties live|Red Book diplomatic code|Black Chamber code token|Zimmermann Telegram code token|Commercial Cable Code token|Bentleys phrase code|Slater telegraphic code|ABC telegraph code"
    list .= "|ADFGVX column key classic|VIC lagged Fibonacci classic|VIC disrupted transposition classic"
    return V28ModeIn(list, name)
}

V30RealWorldLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Trithemius Ave Maria code|Trithemius Polygraphia alphabet|Copiale cipher token|Voynich EVA token|Red Book diplomatic code|Black Chamber code token|Zimmermann Telegram code token|Commercial Cable Code token|Bentleys phrase code|Slater telegraphic code|ABC telegraph code", modeName)
        return V30CodebookToken(letter)

    if V28ModeIn("Alberti disk 1467|Saint-Cyr wheel 1880|Napoleonic field cipher", modeName) {
        shift := shiftValue + V29ModeOffset(modeName) + streamIndex
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Bellaso 1553 reciprocal|Vigenere Beaufort variant historical|Vigenere Beaufort reciprocal|Beaufort Royal Navy", modeName)
        return V28BeaufortClassic(letter)

    if V28ModeIn("Vigenere 1586 autokey", modeName)
        return V28AutoclaveVigenere(letter)

    if V28ModeIn("Porta 1563 table|Porta reciprocal digraph|Porta polyalphabetic 1563", modeName)
        return V28PortaClassic(letter)

    if V28ModeIn("Vigenere running key classic", modeName)
        return V28VigenereClassic(letter)

    if modeName = "Count Gronsfeld cipher" {
        shift := DigitShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Masonic pigpen classic|Rosicrucian cipher classic|Knights Templar cipher classic|Freemason pigpen dotted", modeName)
        return V30SymbolToken(letter)

    if V28ModeIn("Zodiac 408 homophonic style|Zodiac 340 homophonic style", modeName)
        return HomophonicNumberLetter(letter)

    if V28ModeIn("Nihilist substitution Russian", modeName)
        return NihilistLetter(letter)

    if V28ModeIn("Seriated Playfair ACA|Wheatstone cryptograph rotor", modeName)
        return PlayfairLetter(letter)

    if V28ModeIn("Digrafid ACA cipher|Trifid Delastelle 3D", modeName)
        return TrifidCoordinateLetter(letter)

    if V28ModeIn("Bifid Delastelle period 7", modeName)
        return BifidLetter(letter)

    if V28ModeIn("Four-square French army", modeName)
        return FourSquareLetter(letter)

    if V28ModeIn("Two-square German army|Double Playfair WW1", modeName)
        return TwoSquareLetter(letter)

    if V28ModeIn("ADFGX Nebel classic", modeName)
        return KeyedADFGXLetter(letter)

    if V28ModeIn("ADFGVX Nebel classic|ADFGVX column key classic", modeName)
        return KeyedADFGVXLetter(letter)

    if V28ModeIn("Confederate route transposition|Union route transposition|AMSCO ACA cipher|Myszkowski ACA cipher|Nihilist transposition Russian|UBCHI double transposition|UBCHI columnar transposition|Cadenus ACA 25-row|Cadenus transposition variant|Fleissner grille 6x6|Cardan grille Renaissance|Route cipher spiral inward classic|Route cipher spiral outward classic|Columnar irregular classic|Columnar complete classic|Rail fence offset classic|Rail fence W pattern classic|VIC disrupted transposition classic", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Jefferson-Bazeries cylinder", modeName)
        return V28WheelCipherLetter(letter)

    if V28ModeIn("Hebern electric rotor|Kryha Liliput machine|Enigma Railway live|Enigma Tirpitz live|Enigma Zahlwerk live|Typex reflector variant live|SIGABA index rotors live|NEMA Kriegsmobilmachung live|KL-7 ADONIS live|Fialka M-125-3 live|Hagelin C-52 live|Hagelin CD-57 live|M-209-B converter live|Lorenz SZ42A live|Lorenz SZ42B live|Siemens T52a live|Siemens T52e live|Purple sixes-twenties live", modeName)
        return V28MachineStreamLetter(letter)

    if V28ModeIn("VIC lagged Fibonacci classic", modeName)
        return V28ChainAdditionLetter(letter)

    return V28HistoricalToken(letter, V30ShortTag(modeName))
}

V30ShortTag(name) {
    clean := ""
    Loop Parse, name
    {
        ch := A_LoopField
        if ch ~= "^[A-Za-z0-9]$"
            clean .= StrUpper(ch)
    }
    if StrLen(clean) < 3
        clean := "RW30"
    return SubStr(clean, 1, 4)
}

V30CodebookToken(letter) {
    global modeName, keyText
    n := LetterIndex(StrUpper(letter)) + 1
    base := PositiveMod(V28Hash(modeName . keyText), 9000) + 1000
    return "CB" . V28PadLeft(base + n, 5, "0") . " "
}

V30SymbolToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter))
    shapes := ["△","□","◇","○","✕","⬟","⬢","⬣","◐","◑","◒","◓","◔","◕","◖","◗","◧","◨","◩","◪","◆","◇","✦","✧","✩","✪"]
    offset := PositiveMod(V28Hash(modeName), shapes.Length)
    return shapes[PositiveMod(idx + offset, shapes.Length) + 1]
}


; ------------------------------------------------------------
; v31 additional real-world / historical cipher adapters
; ------------------------------------------------------------

IsV31RealWorldMode(name) {
    list := ""
    list .= "Aeneas disk cipher|Polybius torch telegraph|Polybius square Greek classic|Scytale Greek army variant|Caesar Suetonius variant|Augustus shift variant|Trithemius cipher disk|Alberti progressive disk|Bellaso countersign cipher|Della Porta reciprocal alphabet|Vigenere running primer|Vigenere Beaufort table 1710|Beaufort naval table 1857|Gronsfeld numeric aristocrat|Kasiski repeated-key cipher|Babbage autokey cipher|Periodic Gromark ACA|Tri-Digital ACA cipher|Tridigital cipher classic|Nihilist periodic key|Monome-Dinome ACA classic|Baconian biliteral classic|Baconian 24-letter classic|Baconian 26-letter modern|Pollux Morse ACA classic v2|Morbit Morse ACA classic v2|Slidefair ACA classic|Portax ACA cipher|Fractionated Morse ACA classic|Checkerboard ACA cipher"
    list .= "|Digrafid period 5|Doppelkasten German double-box|Double-square vertical classic|Double-square horizontal classic|Foursquare 5x5 classic|Two-square vertical classic|Two-square horizontal classic|Seriated Bifid ACA|CM Bifid ACA|Nihilist transposition ACA|Redefence ACA cipher|Rail fence offset ACA|Columnar cadenus mixed|Interrupted columnar transposition|AMSCO irregular transposition classic|Route cipher clockwise spiral|Route cipher counterclockwise spiral|Turning grille 4x4 classic|Fleissner 8x8 grille|Cardan grille 16th century|Hebern 1921 rotor|Enigma M3 Wehrmacht style|Enigma M4 Triton style|Enigma Uhr box style|British Typex 5-rotor style|SIGABA stepping maze style|NEMA Swiss 10-wheel style|KL-7 ADONIS rotor style|Hagelin M-209 lug cage style|Hagelin C-446 style"
    list .= "|Hagelin CX-52 irregular style|Fialka M-125 wheel style|Siemens T52d style|Lorenz SZ42 chi psi style|Rockex one-time tape style|KW-26 ROMULUS stream style|TSEC/KL-7 token|Kryha Standard machine style|Kryha Liliput pocket style|Nomenclator 1700s diplomatic|Louis XIV Great Cipher style|Rossignols Great Cipher token|Beale cipher book style|Dorabella cipher symbol style|Copiale substitution style|Voynich EVA glyph style|Navajo code talker alphabet|RAF brevity code token|SOE poem code style|Resistance poem code token|Double transposition agent classic|One-time pad five-figure groups|One-time pad five-letter groups|Vernam Baudot tape style|Soviet VIC agent style|DRYAD numeral cipher|BATCO tactical code|SLIDEX tactical code|Brevity codeword token|Commercial codebook 5-letter|Cable code 5-figure"
    return V28ModeIn(list, name)
}

V31RealWorldLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Aeneas disk cipher|Caesar Suetonius variant|Augustus shift variant|Trithemius cipher disk", modeName) {
        shift := shiftValue + V29ModeOffset(modeName) + (modeName = "Trithemius cipher disk" ? streamIndex : 0)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Alberti progressive disk|Bellaso countersign cipher|Vigenere running primer|Kasiski repeated-key cipher", modeName)
        return V28VigenereClassic(letter)

    if V28ModeIn("Della Porta reciprocal alphabet|Vigenere Beaufort table 1710|Beaufort naval table 1857", modeName)
        return V28BeaufortClassic(letter)

    if V28ModeIn("Gronsfeld numeric aristocrat", modeName) {
        shift := DigitShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if modeName = "Babbage autokey cipher"
        return V28AutoclaveVigenere(letter)

    if V28ModeIn("Polybius torch telegraph|Polybius square Greek classic", modeName)
        return PolybiusLetter(letter)

    if V28ModeIn("Monome-Dinome ACA classic|Checkerboard ACA cipher", modeName)
        return StraddlingCheckerboardLetter(letter)

    if V28ModeIn("Baconian biliteral classic|Baconian 24-letter classic|Baconian 26-letter modern", modeName)
        return BaconianLetter(letter)

    if V28ModeIn("Pollux Morse ACA classic v2", modeName)
        return PolluxMorseLetter(letter)

    if V28ModeIn("Morbit Morse ACA classic v2", modeName)
        return MorbitMorseLetter(letter)

    if V28ModeIn("Fractionated Morse ACA classic", modeName)
        return FractionatedMorseLetter(letter)

    if V28ModeIn("Periodic Gromark ACA|Tri-Digital ACA cipher|Tridigital cipher classic|Nihilist periodic key", modeName)
        return V31NumberedCheckerToken(letter)

    if V28ModeIn("Slidefair ACA classic", modeName)
        return SlidefairLetter(letter)

    if V28ModeIn("Portax ACA cipher", modeName)
        return V28PortaClassic(letter)

    if V28ModeIn("Digrafid period 5", modeName)
        return TrifidCoordinateLetter(letter)

    if V28ModeIn("Doppelkasten German double-box|Double-square vertical classic|Two-square vertical classic", modeName)
        return TwoSquareLetter(letter)

    if V28ModeIn("Double-square horizontal classic|Two-square horizontal classic", modeName)
        return TwoSquareLetter(letter)

    if V28ModeIn("Foursquare 5x5 classic", modeName)
        return FourSquareLetter(letter)

    if V28ModeIn("Seriated Bifid ACA|CM Bifid ACA", modeName)
        return BifidLetter(letter)

    if V28ModeIn("Scytale Greek army variant|Nihilist transposition ACA|Redefence ACA cipher|Rail fence offset ACA|Columnar cadenus mixed|Interrupted columnar transposition|AMSCO irregular transposition classic|Route cipher clockwise spiral|Route cipher counterclockwise spiral|Turning grille 4x4 classic|Fleissner 8x8 grille|Cardan grille 16th century|Double transposition agent classic", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Hebern 1921 rotor|Enigma M3 Wehrmacht style|Enigma M4 Triton style|Enigma Uhr box style|British Typex 5-rotor style|SIGABA stepping maze style|NEMA Swiss 10-wheel style|KL-7 ADONIS rotor style|Hagelin M-209 lug cage style|Hagelin C-446 style|Hagelin CX-52 irregular style|Fialka M-125 wheel style|Siemens T52d style|Lorenz SZ42 chi psi style|Rockex one-time tape style|KW-26 ROMULUS stream style|Kryha Standard machine style|Kryha Liliput pocket style", modeName)
        return V28MachineStreamLetter(letter)

    if V28ModeIn("One-time pad five-figure groups", modeName)
        return V31OtpGroupToken(letter, true)

    if V28ModeIn("One-time pad five-letter groups", modeName)
        return V31OtpGroupToken(letter, false)

    if V28ModeIn("Vernam Baudot tape style|Soviet VIC agent style", modeName)
        return V28StreamXorToken(letter)

    if V28ModeIn("Dorabella cipher symbol style|Copiale substitution style|Voynich EVA glyph style", modeName)
        return V31HistoricalSymbol(letter)

    if V28ModeIn("Nomenclator 1700s diplomatic|Louis XIV Great Cipher style|Rossignols Great Cipher token|Beale cipher book style|Navajo code talker alphabet|RAF brevity code token|SOE poem code style|Resistance poem code token|DRYAD numeral cipher|BATCO tactical code|SLIDEX tactical code|Brevity codeword token|Commercial codebook 5-letter|Cable code 5-figure|TSEC/KL-7 token", modeName)
        return V31CodebookToken(letter)

    return V28HistoricalToken(letter, V31ShortTag(modeName))
}

V31ShortTag(name) {
    clean := ""
    Loop Parse, name
    {
        ch := A_LoopField
        if ch ~= "^[A-Za-z0-9]$"
            clean .= StrUpper(ch)
    }
    if StrLen(clean) < 3
        clean := "RW31"
    return SubStr(clean, 1, 5)
}

V31CodebookToken(letter) {
    global modeName, keyText
    idx := LetterIndex(StrUpper(letter)) + 1
    base := PositiveMod(V28Hash(modeName . ":" . keyText), 80000) + 10000
    if V28ModeIn("Commercial codebook 5-letter|One-time pad five-letter groups|Navajo code talker alphabet", modeName)
        return V31FiveLetterGroup(base + idx) . " "
    if V28ModeIn("DRYAD numeral cipher|BATCO tactical code|SLIDEX tactical code|Cable code 5-figure|Louis XIV Great Cipher style|Rossignols Great Cipher token", modeName)
        return V28PadLeft(PositiveMod(base + idx, 100000), 5, "0") . " "
    words := ["ABLE", "BAKER", "CIPHER", "DELTA", "EAGLE", "FALCON", "GAMMA", "HARBOR", "IRON", "JUPITER", "KILO", "LANTERN", "MERCURY", "NORTH", "ORBIT", "PAPER", "QUARTZ", "RIVER", "SIGNAL", "TOWER", "UNION", "VICTOR", "WINTER", "XENON", "YARD", "ZEBRA"]
    return words[idx] . "-" . V28PadLeft(PositiveMod(base, 999), 3, "0") . " "
}

V31FiveLetterGroup(n) {
    n := PositiveMod(n, 11881376)
    out := ""
    Loop 5 {
        qr := DivModCompat(n, 26)
        n := qr[1]
        r := qr[2]
        out := Chr(65 + r) . out
    }
    return out
}

DivModCompat(n, d) {
    q := Floor(n / d)
    r := n - (q * d)
    return [q, r]
}

V31OtpGroupToken(letter, numeric := true) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    pad := PositiveMod(V28Hash(modeName . keyText . streamIndex), numeric ? 100000 : 11881376)
    streamIndex += 1
    if numeric
        return V28PadLeft(PositiveMod((idx * 307) + pad, 100000), 5, "0") . " "
    return V31FiveLetterGroup((idx * 4099) + pad) . " "
}

V31NumberedCheckerToken(letter) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    k := PositiveMod(V28Hash(keyText . modeName) + streamIndex * 7, 90) + 10
    streamIndex += 1
    return V31ShortTag(modeName) . V28PadLeft(idx + k, 3, "0") . " "
}

V31HistoricalSymbol(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter))
    dorabella := ["⊂", "⊃", "⊏", "⊐", "◜", "◝", "◞", "◟", "⌜", "⌝", "⌞", "⌟", "△", "▽", "◇", "○", "◐", "◑", "◒", "◓", "◔", "◕", "✶", "✷", "✸", "✹"]
    eva := ["q", "o", "k", "y", "d", "a", "i", "n", "s", "h", "e", "t", "r", "l", "p", "f", "c", "g", "m", "b", "v", "x", "z", "ch", "sh", "ee"]
    if InStr(modeName, "Voynich")
        return eva[idx + 1] . " "
    off := PositiveMod(V28Hash(modeName), dorabella.Length)
    return dorabella[PositiveMod(idx + off, dorabella.Length) + 1]
}


; ------------------------------------------------------------
; v32 additional real-world / practical cipher adapters
; ------------------------------------------------------------

IsV32MoreMode(name) {
    list := ""
    list .= "Quagmire I ACA classic|Quagmire II ACA classic|Quagmire III ACA classic|Quagmire IV ACA classic|Porta progressive table classic|Porta reciprocal 1563|Alberti shifting alphabet 1467|Trithemius Ave Maria numeric|Bellaso 1564 countersign|Vigenere square 19th-century|Gronsfeld decimal key classic|Beaufort naval reciprocal v2|Variant Beaufort reciprocal v2|Diana one-time pad classic|Vernam mod-26 letters|Playfair Australian Army|Playfair RAAF 6x6|Double Playfair Wehrmacht|Two-square horizontal Delastelle|Four-square French classic|Bifid period 10 Delastelle|Trifid period 10 Delastelle|Tri-square Delastelle token|Nihilist substitution Soviet|Nihilist Polybius overadditive|Gromark running digits|Aristocrat simple substitution|Patristocrat no spaces|Xenocrypt alphabet token|Headline puzzle ACA|Route transposition rail variant|Route transposition diagonal|Route transposition spiral alternate|Rail fence 4-rail classic|Rail fence 5-rail classic|Cadenus 25-row ACA|AMSCO alternating 1-2|Swagman permutation classic|Myszkowski repeated-key classic|Enigma M3 naval style live|Enigma M4 shark style live|Enigma D commercial style live|Typex plugboard style live|SIGABA cipher maze live|Hagelin BC-38 style live|Hagelin C-36 style live|Hagelin C-38 style live|Hagelin CX-52 style live|Siemens T52c style live|Lorenz SZ40 chi wheel live|Lorenz SZ42 psi wheel live|Purple 6-20 switch live|Red machine diplomatic live|Green cipher machine live|Hebern five-rotor style live|Kryha electric style live"
    list .= "|NATO ACP-131 brevity token|Q-code telegraph token|Z-code telegraph token|Phillips code naval token|International Code of Signals flag token|US Army brevity code token|Allied call sign token|SOE silk code token|Poem code transposition token|Book cipher chapter-verse token|Dictionary code page-line-word|Nomenclator syllable code|Diplomatic four-figure code|Diplomatic five-figure code|Commercial cable pronounceable code|Morse landline American|Wigwag flag code|Chappe semaphore numbered|Optical telegraph station code|Heliograph Morse field code|ADFGX columnar classic v2|ADFGVX mixed square classic|VIC additive checkerboard v2|VIC transposition phase token|DRYAD two-digit table v2|BATCO phrase table v2|SLIDEX row-column v2|Brevity code ACP token|One-time pad decimal groups|One-time pad letter groups v2|Pigpen Freemason classic v2|Rosicrucian grid classic v2|Templar cross cipher v2|Gold-Bug Poe symbols v2|Dorabella curved symbols v2|Copiale homophonic token v2|Zodiac homophonic 340 style v2|Beale book number token v2|Voynich EVA transliteration v2|Runic cipher medieval token"
    return V28ModeIn(list, name)
}

V32MoreLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Quagmire I ACA classic", modeName)
        return QuagmireLetter(letter, 1)
    if V28ModeIn("Quagmire II ACA classic", modeName)
        return QuagmireLetter(letter, 2)
    if V28ModeIn("Quagmire III ACA classic", modeName)
        return QuagmireLetter(letter, 3)
    if V28ModeIn("Quagmire IV ACA classic", modeName)
        return QuagmireLetter(letter, 4)

    if V28ModeIn("Porta progressive table classic|Porta reciprocal 1563", modeName)
        return V28PortaClassic(letter)

    if V28ModeIn("Alberti shifting alphabet 1467", modeName)
        return AlbertiDiskLetter(letter)

    if V28ModeIn("Trithemius Ave Maria numeric", modeName) {
        shift := streamIndex
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Bellaso 1564 countersign|Vigenere square 19th-century|Gromark running digits|Vernam mod-26 letters", modeName)
        return V28VigenereClassic(letter)

    if V28ModeIn("Gronsfeld decimal key classic", modeName) {
        shift := DigitShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Beaufort naval reciprocal v2", modeName)
        return V28BeaufortClassic(letter)

    if V28ModeIn("Variant Beaufort reciprocal v2", modeName) {
        shift := KeyShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, -shift)
    }

    if V28ModeIn("Diana one-time pad classic", modeName)
        return DianaLetter(letter)

    if V28ModeIn("Playfair Australian Army|Double Playfair Wehrmacht", modeName)
        return PlayfairLetter(letter)

    if V28ModeIn("Playfair RAAF 6x6", modeName)
        return Playfair6x6Letter(letter)

    if V28ModeIn("Two-square horizontal Delastelle", modeName)
        return TwoSquareLetter(letter)

    if V28ModeIn("Four-square French classic", modeName)
        return FourSquareLetter(letter)

    if V28ModeIn("Bifid period 10 Delastelle", modeName)
        return BifidLetter(letter)

    if V28ModeIn("Trifid period 10 Delastelle", modeName)
        return TrifidFullPeriodLetter(letter)

    if V28ModeIn("Tri-square Delastelle token", modeName)
        return TriSquareLetter(letter)

    if V28ModeIn("Nihilist substitution Soviet|Nihilist Polybius overadditive", modeName)
        return NihilistLetter(letter)

    if V28ModeIn("Aristocrat simple substitution|Patristocrat no spaces|Xenocrypt alphabet token", modeName)
        return V32SubstitutionStyle(letter)

    if V28ModeIn("Headline puzzle ACA|Null cipher acrostic classic|Null cipher every third", modeName)
        return V32NullCipherToken(letter)

    if V28ModeIn("Route transposition rail variant|Route transposition diagonal|Route transposition spiral alternate|Rail fence 4-rail classic|Rail fence 5-rail classic|Cadenus 25-row ACA|AMSCO alternating 1-2|Swagman permutation classic|Myszkowski repeated-key classic|VIC transposition phase token|Poem code transposition token", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Enigma M3 naval style live|Enigma M4 shark style live|Enigma D commercial style live|Typex plugboard style live|SIGABA cipher maze live|Hagelin BC-38 style live|Hagelin C-36 style live|Hagelin C-38 style live|Hagelin CX-52 style live|Siemens T52c style live|Lorenz SZ40 chi wheel live|Lorenz SZ42 psi wheel live|Purple 6-20 switch live|Red machine diplomatic live|Green cipher machine live|Hebern five-rotor style live|Kryha electric style live", modeName)
        return V28MachineStreamLetter(letter)

    if V28ModeIn("ADFGX columnar classic v2", modeName)
        return KeyedADFGXLetter(letter)

    if V28ModeIn("ADFGVX mixed square classic", modeName)
        return KeyedADFGVXLetter(letter)

    if V28ModeIn("VIC additive checkerboard v2", modeName)
        return V28ChainAdditionLetter(letter)

    if V28ModeIn("One-time pad decimal groups", modeName)
        return V31OtpGroupToken(letter, true)

    if V28ModeIn("One-time pad letter groups v2", modeName)
        return V31OtpGroupToken(letter, false)

    if V28ModeIn("Morse landline American|Wigwag flag code|Chappe semaphore numbered|Optical telegraph station code|Heliograph Morse field code", modeName)
        return V32SignalToken(letter)

    if V28ModeIn("Pigpen Freemason classic v2|Rosicrucian grid classic v2|Templar cross cipher v2|Gold-Bug Poe symbols v2|Dorabella curved symbols v2|Copiale homophonic token v2|Zodiac homophonic 340 style v2|Voynich EVA transliteration v2|Runic cipher medieval token", modeName)
        return V32SymbolToken(letter)

    if V28ModeIn("NATO ACP-131 brevity token|Q-code telegraph token|Z-code telegraph token|Phillips code naval token|International Code of Signals flag token|US Army brevity code token|Allied call sign token|SOE silk code token|Book cipher chapter-verse token|Dictionary code page-line-word|Nomenclator syllable code|Diplomatic four-figure code|Diplomatic five-figure code|Commercial cable pronounceable code|DRYAD two-digit table v2|BATCO phrase table v2|SLIDEX row-column v2|Brevity code ACP token|Beale book number token v2", modeName)
        return V32CodeToken(letter)

    return V28HistoricalToken(letter, V32ShortTag(modeName))
}

V32ShortTag(name) {
    clean := ""
    Loop Parse, name
    {
        ch := A_LoopField
        if ch ~= "^[A-Za-z0-9]$"
            clean .= StrUpper(ch)
    }
    if StrLen(clean) < 4
        clean := clean . "V32X"
    return SubStr(clean, 1, 4)
}

V32SubstitutionStyle(letter) {
    global modeName, keyText
    if modeName = "Patristocrat no spaces"
        return SubstituteFromAlphabet(letter, KeywordAlphabet(keyText . "PATRISTOCRAT"))
    if modeName = "Xenocrypt alphabet token"
        return "[XE" . V28PadLeft(LetterIndex(StrUpper(letter)) + 1, 2, "0") . "] "
    return SubstituteFromAlphabet(letter, KeywordAlphabet(keyText . modeName))
}

V32NullCipherToken(letter) {
    global modeName, streamIndex
    u := StrUpper(letter)
    idx := LetterIndex(u) + 1
    streamIndex += 1
    if modeName = "Null cipher every third"
        return "xx" . StrLower(u)
    if modeName = "Null cipher acrostic classic"
        return u . "cover "
    words := ["Alpha", "Bravo", "Cipher", "Delta", "Eagle", "Falcon", "Gamma", "Harbor", "Iron", "Jolly", "Kilo", "Lima", "Mason", "North", "Orbit", "Paper", "Quartz", "River", "Signal", "Tower", "Union", "Victor", "Winter", "Xray", "Yankee", "Zebra"]
    return words[idx] . " "
}

V32SignalToken(letter) {
    global modeName
    u := StrUpper(letter)
    idx := LetterIndex(u) + 1
    if InStr(modeName, "Morse") || InStr(modeName, "Heliograph")
        return MorseLetter(letter)
    if InStr(modeName, "Wigwag")
        return "[WG" . V28PadLeft(idx, 2, "0") . "] "
    if InStr(modeName, "Chappe")
        return "[CH" . V28PadLeft(idx + 100, 3, "0") . "] "
    return "[OT" . V28PadLeft(idx, 2, "0") . "] "
}

V32SymbolToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter))
    if InStr(modeName, "Voynich") {
        eva := ["qo", "ol", "dy", "ai", "in", "ee", "ch", "sh", "or", "ar", "yk", "dal", "ched", "qok", "ot", "ok", "yte", "iin", "qot", "qoky", "olai", "dain", "chey", "sho", "qoke", "otee"]
        return eva[idx + 1] . " "
    }
    if InStr(modeName, "Runic")
        return ElderFutharkLetter(letter)
    syms := ["☉", "☽", "☿", "♀", "♂", "♃", "♄", "♈", "♉", "♊", "♋", "♌", "♍", "♎", "♏", "♐", "♑", "♒", "♓", "✠", "✥", "✦", "✧", "✩", "✪", "✫"]
    off := PositiveMod(V28Hash(modeName), syms.Length)
    return syms[PositiveMod(idx + off, syms.Length) + 1]
}

ElderFutharkLetter(letter) {
    u := StrUpper(letter)
    runes := "ᚨᛒᚲᛞᛖᚠᚷᚺᛁᛃᚲᛚᛗᚾᛟᛈᚲᚱᛊᛏᚢᚹᚹᛉᛇᛉ"
    idx := LetterIndex(u)
    return SubStr(runes, idx + 1, 1)
}

V32CodeToken(letter) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    seed := PositiveMod(V28Hash(modeName . keyText . streamIndex), 90000) + 10000
    streamIndex += 1
    if InStr(modeName, "four-figure")
        return V28PadLeft(PositiveMod(seed + idx, 10000), 4, "0") . " "
    if InStr(modeName, "five-figure") || InStr(modeName, "DRYAD") || InStr(modeName, "BATCO") || InStr(modeName, "SLIDEX")
        return V28PadLeft(PositiveMod(seed + idx, 100000), 5, "0") . " "
    if InStr(modeName, "Q-code")
        return "Q" . Chr(65 + PositiveMod(idx + streamIndex, 26)) . Chr(65 + PositiveMod(seed, 26)) . " "
    if InStr(modeName, "Z-code")
        return "Z" . Chr(65 + PositiveMod(idx + streamIndex, 26)) . Chr(65 + PositiveMod(seed, 26)) . " "
    if InStr(modeName, "cable") || InStr(modeName, "Commercial")
        return V31FiveLetterGroup(seed + idx) . " "
    return V32ShortTag(modeName) . "-" . V28PadLeft(idx, 2, "0") . " "
}


; ------------------------------------------------------------
; v33 additional real-world / historical cipher adapters
; ------------------------------------------------------------

IsV33RealWorldMode(name) {
    list := "Delastelle Bifid classic period 5|Delastelle Trifid classic period 5|Delastelle Four-square military|Wheatstone-Playfair digraph v2|German Doppelkasten horizontal|German Doppelkasten vertical|Nihilist cipher overaddition v2|Nihilist checkerboard prisoner|Pollux fractionated Morse classic|Morbit ACA classic v2|Fractionated Morse ACA v2|ADFGX Western Front variant|ADFGVX radio traffic variant|GEDEFU 36-coordinate cipher|Seriated Playfair period 6|Myszkowski transposition ACA v2|Cadenus ACA v2|Swagman ACA v2|Redefence ACA rail cipher|Route cipher snake route|Cardan grille 6x6 classic|Fleissner grille 8x8 classic|Turning grille Russian style|Double transposition agent style|Phillips cipher ACA v2|Phillips RC variant v2|Bifid cipher period 7|Trifid cipher period 7|Gromark running key ACA|Periodic Gromark v2|Quagmire I army style|Quagmire II army style|Quagmire III army style|Quagmire IV army style|Porta key-table variant|Beaufort naval reciprocal 1915|Variant Beaufort German style|Bellaso progressive countersign|Vigenere reciprocal table variant|Vigenere autokey historical v2|Gronsfeld courier key|Trithemius progressive alphabet v2|Alberti disk changing indicator|Saint-Cyr slide alphabet v2|Confederate cipher wheel v2|Union cipher wheel v2|Hebern one-rotor simulator|Kryha machine stepping v2|Enigma Uhr switch style|Enigma M4 U-boat shark key|Typex crib-resistant style|SIGABA CSP-889 style|NEMA 1947 style|Fialka Cyrillic wheel style|KL-7 ADONIS style|Hagelin M-209 lug pin v2|Hagelin C-52 pinwheel v2|Lorenz SZ42 teleprinter v2|Siemens T52 Sturgeon style|Purple stepping switches v2|Vernam teleprinter XOR tape v2|One-time pad diplomatic 5-groups|Soviet OTP number station style|Numbers station five-digit groups|DRYAD tactical numeral v3|BATCO tactical phrase v3"
    list .= "|SLIDEX battlefield row-col v3|Brevity code aviation ACP|QNH Q-code token|ZBK Z-code token|International Morse 1865|American Morse railroad v2|Wigwag Myer code v2|Chappe optical telegraph v2|Heliograph field Morse v2|Naval flag hoist ICS v2|Semaphore flag pair v2|NATO spelling alphabet official|APCO Project 14 radio code|PGP word list token|S/KEY one-time password words|Nomenclator syllable 1800s|Rossignol syllable token|Great Cipher syllable-number v2|Louis XIV nomenclator v2|Beale cipher Declaration book v2|Dorabella cipher Elgar style|Gold-Bug substitution Poe v3|Zodiac 408 exact-ish style|Zodiac 340 transposition style|Copiale code glyph token v3|Voynich EVA diplomatic|Runic cipher twig rune token|Ogham cipher medieval v2|Templar cipher cross token v3|Pigpen Masonic dotted v3|Rosicrucian cipher grid v3|Monome-dinome checkerboard WWI|Bacon biliteral Francis Bacon 1623|Bacon twenty-four-letter alphabet|Semaphore naval alphabet 1795|Morse Continental code 1848|Field cipher disk M-138 style|US Army M-94 strip variant|Jefferson wheel 1795 variant|Bazeries 1891 cylinder variant|VIC agent checkerboard variant|DRYAD KTC 1400 style|BATCO map coordinate style|Slidex message card style|Poem code SOE style|Silk code escape map style|Five-letter code group diplomatic|Five-figure code group diplomatic|Commercial cable code pronounceable v2|Naval code flag group token|Weather ship code token|Phillips naval code word v2"
    return V28ModeIn(list, name)
}

V33RealWorldLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Quagmire I army style", modeName)
        return QuagmireLetter(letter, 1)
    if V28ModeIn("Quagmire II army style", modeName)
        return QuagmireLetter(letter, 2)
    if V28ModeIn("Quagmire III army style", modeName)
        return QuagmireLetter(letter, 3)
    if V28ModeIn("Quagmire IV army style", modeName)
        return QuagmireLetter(letter, 4)

    if V28ModeIn("Bellaso progressive countersign|Vigenere reciprocal table variant|Gronsfeld courier key|Vigenere autokey historical v2|Porta key-table variant|Trithemius progressive alphabet v2", modeName) {
        if InStr(modeName, "Gronsfeld") {
            shift := DigitShiftAt(keyText, streamIndex)
            streamIndex += 1
            return ShiftLetter(letter, shift)
        }
        if InStr(modeName, "autokey") || InStr(modeName, "Autokey") {
            shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
            streamIndex += 1
            autoKeyHistory .= StrUpper(letter)
            return ShiftLetter(letter, shift)
        }
        if InStr(modeName, "Trithemius") {
            shift := streamIndex
            streamIndex += 1
            return ShiftLetter(letter, shift)
        }
        if InStr(modeName, "Porta")
            return V28PortaClassic(letter)
        return V28VigenereClassic(letter)
    }

    if V28ModeIn("Beaufort naval reciprocal 1915|Variant Beaufort German style", modeName) {
        if InStr(modeName, "Variant") {
            shift := KeyShiftAt(keyText, streamIndex)
            streamIndex += 1
            return ShiftLetter(letter, -shift)
        }
        return V28BeaufortClassic(letter)
    }

    if V28ModeIn("Alberti disk changing indicator|Saint-Cyr slide alphabet v2|Confederate cipher wheel v2|Union cipher wheel v2", modeName) {
        shift := shiftValue + V29ModeOffset(modeName) + streamIndex
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Delastelle Bifid classic period 5|Bifid cipher period 7", modeName)
        return BifidLetter(letter)
    if V28ModeIn("Delastelle Trifid classic period 5|Trifid cipher period 7", modeName)
        return TrifidFullPeriodLetter(letter)
    if V28ModeIn("Delastelle Four-square military", modeName)
        return FourSquareLetter(letter)
    if V28ModeIn("Wheatstone-Playfair digraph v2|Seriated Playfair period 6", modeName)
        return PlayfairLetter(letter)
    if V28ModeIn("German Doppelkasten horizontal|German Doppelkasten vertical", modeName)
        return TwoSquareLetter(letter)
    if V28ModeIn("Phillips cipher ACA v2|Phillips RC variant v2", modeName)
        return PhillipsLetter(letter)

    if V28ModeIn("Nihilist cipher overaddition v2|Nihilist checkerboard prisoner", modeName)
        return NihilistLetter(letter)
    if V28ModeIn("Gromark running key ACA|Periodic Gromark v2", modeName)
        return GromarkLetter(letter)
    if V28ModeIn("ADFGX Western Front variant", modeName)
        return KeyedADFGXLetter(letter)
    if V28ModeIn("ADFGVX radio traffic variant|GEDEFU 36-coordinate cipher", modeName)
        return KeyedADFGVXLetter(letter)
    if V28ModeIn("Monome-dinome checkerboard WWI", modeName)
        return MonomeDinomeLetter(letter)
    if V28ModeIn("Bacon biliteral Francis Bacon 1623|Bacon twenty-four-letter alphabet", modeName)
        return BaconianLetter(letter)
    if V28ModeIn("Pollux fractionated Morse classic", modeName)
        return PolluxMorseLetter(letter)
    if V28ModeIn("Morbit ACA classic v2", modeName)
        return MorbitMorseLetter(letter)
    if V28ModeIn("Fractionated Morse ACA v2", modeName)
        return FractionatedMorseLetter(letter)

    if V28ModeIn("Myszkowski transposition ACA v2|Cadenus ACA v2|Swagman ACA v2|Redefence ACA rail cipher|Route cipher clockwise spiral|Route cipher snake route|Cardan grille 6x6 classic|Fleissner grille 8x8 classic|Turning grille Russian style|Double transposition agent style", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Hebern one-rotor simulator|Kryha machine stepping v2|Enigma Uhr switch style|Enigma M4 U-boat shark key|Typex crib-resistant style|SIGABA CSP-889 style|NEMA 1947 style|Fialka Cyrillic wheel style|KL-7 ADONIS style|Hagelin M-209 lug pin v2|Hagelin C-52 pinwheel v2|Lorenz SZ42 teleprinter v2|Siemens T52 Sturgeon style|Purple stepping switches v2", modeName)
        return V28MachineStreamLetter(letter)

    if V28ModeIn("Vernam teleprinter XOR tape v2", modeName)
        return VernamXor5BitLetter(letter)
    if V28ModeIn("One-time pad diplomatic 5-groups|Soviet OTP number station style|Numbers station five-digit groups", modeName)
        return V31OtpGroupToken(letter, true)
    if V28ModeIn("DRYAD tactical numeral v3|BATCO tactical phrase v3|SLIDEX battlefield row-col v3|Brevity code aviation ACP|QNH Q-code token|ZBK Z-code token|Nomenclator syllable 1800s|Rossignol syllable token|Great Cipher syllable-number v2|Louis XIV nomenclator v2|Beale cipher Declaration book v2|PGP word list token|S/KEY one-time password words|Five-letter code group diplomatic|Five-figure code group diplomatic|Commercial cable code pronounceable v2|Naval code flag group token|Weather ship code token|Phillips naval code word v2", modeName)
        return V33CodeToken(letter)

    if V28ModeIn("International Morse 1865|American Morse railroad v2|Wigwag Myer code v2|Chappe optical telegraph v2|Heliograph field Morse v2|Naval flag hoist ICS v2|Semaphore flag pair v2|Semaphore naval alphabet 1795|Morse Continental code 1848", modeName)
        return V33SignalToken(letter)

    if V28ModeIn("NATO spelling alphabet official", modeName)
        return NatoLetter(letter)
    if V28ModeIn("APCO Project 14 radio code", modeName)
        return V33APCOWord(letter)

    if V28ModeIn("Dorabella cipher Elgar style|Gold-Bug substitution Poe v3|Zodiac 408 exact-ish style|Zodiac 340 transposition style|Copiale code glyph token v3|Voynich EVA diplomatic|Runic cipher twig rune token|Ogham cipher medieval v2|Templar cipher cross token v3|Pigpen Masonic dotted v3|Rosicrucian cipher grid v3", modeName)
        return V33SymbolToken(letter)

    if V28ModeIn("Field cipher disk M-138 style|US Army M-94 strip variant|Jefferson wheel 1795 variant|Bazeries 1891 cylinder variant|VIC agent checkerboard variant|DRYAD KTC 1400 style|BATCO map coordinate style|Slidex message card style|Poem code SOE style|Silk code escape map style", modeName)
        return V33CodeToken(letter)

    return V28HistoricalToken(letter, V33ShortTag(modeName))
}

V33ShortTag(name) {
    clean := ""
    Loop Parse, name
    {
        ch := A_LoopField
        if ch ~= "^[A-Za-z0-9]$"
            clean .= StrUpper(ch)
    }
    if StrLen(clean) < 4
        clean .= "V33X"
    return SubStr(clean, 1, 4)
}

V33CodeToken(letter) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    seed := PositiveMod(V28Hash(modeName . keyText . streamIndex), 99999)
    streamIndex += 1
    if InStr(modeName, "five-letter") || InStr(modeName, "Commercial") || InStr(modeName, "PGP") || InStr(modeName, "S/KEY")
        return V31FiveLetterGroup(seed + idx) . " "
    if InStr(modeName, "four") || InStr(modeName, "Great Cipher") || InStr(modeName, "Louis XIV")
        return V28PadLeft(PositiveMod(seed + idx, 10000), 4, "0") . " "
    if InStr(modeName, "QNH")
        return "QNH" . V28PadLeft(PositiveMod(idx + seed, 100), 2, "0") . " "
    if InStr(modeName, "ZBK")
        return "ZBK" . V28PadLeft(PositiveMod(idx + seed, 100), 2, "0") . " "
    return V33ShortTag(modeName) . "-" . V28PadLeft(idx, 2, "0") . " "
}

V33SignalToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter)) + 1
    if InStr(modeName, "Morse") || InStr(modeName, "Heliograph")
        return MorseLetter(letter)
    if InStr(modeName, "Semaphore")
        return "[SEM" . V28PadLeft(idx, 2, "0") . "] "
    if InStr(modeName, "Wigwag")
        return "[WIG" . V28PadLeft(idx, 2, "0") . "] "
    if InStr(modeName, "Chappe")
        return "[CHP" . V28PadLeft(idx + 100, 3, "0") . "] "
    if InStr(modeName, "flag") || InStr(modeName, "Naval")
        return MaritimeFlagLetter(letter)
    return "[SIG" . V28PadLeft(idx, 2, "0") . "] "
}

V33SymbolToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter))
    if InStr(modeName, "Runic")
        return ElderFutharkLetter(letter)
    if InStr(modeName, "Ogham")
        return OghamLetter(letter)
    if InStr(modeName, "Voynich") {
        eva := ["qo", "ol", "dy", "ai", "in", "ee", "ch", "sh", "or", "ar", "yk", "dal", "ched", "qok", "ot", "ok", "yte", "iin", "qot", "qoky", "olai", "dain", "chey", "sho", "qoke", "otee"]
        return eva[idx + 1] . " "
    }
    syms := ["☉", "☽", "☿", "♀", "♂", "♃", "♄", "♈", "♉", "♊", "♋", "♌", "♍", "♎", "♏", "♐", "♑", "♒", "♓", "✠", "✥", "✦", "✧", "✩", "✪", "✫"]
    off := PositiveMod(V28Hash(modeName), syms.Length)
    return syms[PositiveMod(idx + off, syms.Length) + 1]
}

V33APCOWord(letter) {
    idx := LetterIndex(StrUpper(letter)) + 1
    words := ["Adam", "Boy", "Charles", "David", "Edward", "Frank", "George", "Henry", "Ida", "John", "King", "Lincoln", "Mary", "Nora", "Ocean", "Paul", "Queen", "Robert", "Sam", "Tom", "Union", "Victor", "William", "X-ray", "Young", "Zebra"]
    return words[idx] . " "
}



; ------------------------------------------------------------
; v34 additional real-world / historical cipher adapters
; ------------------------------------------------------------

IsV34RealWorldMode(name) {
    list := "Caesar ROT5 digits classic|Caesar ROT18 alphanumeric classic|Caesar ROT25 inverse classic|Polybius torch code Latin|Polybius 6x6 military checkerboard|Trithemius recta Latin classic|Trithemius progressive keyed recta|Alberti numeric indicator disk|Alberti periodic indicator disk|Porta disk diplomatic variant|Della Porta reciprocal disk v2|Bellaso cipher with countersign v3|Vigenere running primer v2|Vigenere Beaufort mixed alphabet v2|Beaufort army field key|Gronsfeld Venetian numeric variant|Autoclave cipher historical v2|Beaufort autoclave historical|Kasiski keyed Vigenere variant|Bazeries number-key classic v2|Chaocipher alphabet classic v2|Phillips plaintext slide variant|Phillips ciphertext slide variant|Doppelkasten checkerboard keyed|Digrafid German field style|Nihilist checkerboard overadd v3|Nihilist columnar transposition style|Bifid fractionating period 3|Bifid fractionating period 9|Trifid fractionating period 3|Trifid fractionating period 9|ADFGX keyed Polybius field|ADFGVX alphanumeric field v2|Monome-Dinome French army variant|Straddling checkerboard decimal variant|VIC sequential transposition style|VIC agent pad groups v2|Interrupted columnar WWI variant|Myszkowski commercial variant|Double columnar agent variant|Rail fence 6-rail classic|Rail fence 7-rail classic|Turning grille 6x6 Austro-Hungarian|Cardan grille Venetian style|AMSCO period-2 classic|Cadenus ACA variant B|Gromark keyed primer variant|Ragbaby period-word start variant"
    list .= "|Nicodemus transposition Vigenere v2|Seriated Playfair period 8|Portax ACA variant|Slidefair ACA variant v2|Four-square Delastelle variant v2|Two-square German field variant|Tri-square ACA classic|Homophonic nomenclator 1400s|Beale variant book cipher|Dorabella symbol alphabet v2|Freemason pigpen X-grid|Templar pigpen dotted cross|Rosicrucian dotted grid|Zodiac 408 homophonic table v3|Zodiac 340 diagonal read style|Copiale homophonic codebook|Voynich Currier glyph token|Navajo code talker word v2|Choctaw code talker token|Q-code maritime token|Z-code military token|Ten-code police radio token|NATO brevity code token v2|ICS flag hoist two-letter|Semaphore field flag token|Wigwag single-flag token|American Morse spaced token|International Morse spaced token|Baudot ITA2 figures-letters field|Murray code teleprinter field|Vernam Baudot XOR field|OTP subtractive letter groups|OTP additive number groups|Numbers station Cyrillic style token|Commercial codebook four-letter|Slater code word variant|Bentley code word variant|ABC code word variant|Zimmermann cable code variant|Diplomatic four-digit book code|Diplomatic five-letter book code|Weather SYNOP code token|Naval signal book token|Army map grid code token|SOE poem transposition v2|Resistance grille code token|Silk code miniature map token|Enigma M3 army daily key|Enigma M4 weather key|Enigma Abwehr G style v2|Typex Mark VI style|SIGABA CSP-2900 style|NEMA training key style|Fialka Latin wheel style|KL-7 training key style"
    list .= "|Hagelin C-36 pin-lug style|Hagelin CD-57 pocket style v2|Siemens T52ca style|Lorenz SZ42c style|Purple diplomatic 1939 style|Red-Orange Japanese machine style|Rockex II tape style|KW-7 ORESTES stream style"
    return V28ModeIn(list, name)
}

V34RealWorldLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex, autoKeyHistory

    if V28ModeIn("Caesar ROT5 digits classic|Caesar ROT18 alphanumeric classic|Caesar ROT25 inverse classic", modeName)
        return V34CaesarFamily(letter)

    if V28ModeIn("Trithemius recta Latin classic|Trithemius progressive keyed recta|Alberti numeric indicator disk|Alberti periodic indicator disk|Saint-Cyr slide alphabet v2", modeName) {
        shift := shiftValue + streamIndex + V29ModeOffset(modeName)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Vigenere running primer v2|Bellaso cipher with countersign v3|Vigenere Beaufort mixed alphabet v2|Kasiski keyed Vigenere variant", modeName)
        return V28VigenereClassic(letter)

    if V28ModeIn("Beaufort army field key|Beaufort autoclave historical", modeName)
        return V28BeaufortClassic(letter)

    if V28ModeIn("Gronsfeld Venetian numeric variant", modeName) {
        shift := DigitShiftAt(keyText, streamIndex)
        streamIndex += 1
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Autoclave cipher historical v2", modeName) {
        shift := AutoKeyShiftAt(keyText, streamIndex, autoKeyHistory)
        streamIndex += 1
        autoKeyHistory .= StrUpper(letter)
        return ShiftLetter(letter, shift)
    }

    if V28ModeIn("Porta disk diplomatic variant|Della Porta reciprocal disk v2", modeName)
        return V28PortaClassic(letter)

    if V28ModeIn("Bazeries number-key classic v2", modeName)
        return BazeriesCylinderLetter(letter)

    if V28ModeIn("Chaocipher alphabet classic v2", modeName)
        return ChaocipherLetter(letter)

    if V28ModeIn("Phillips plaintext slide variant|Phillips ciphertext slide variant", modeName)
        return PhillipsLetter(letter)

    if V28ModeIn("Doppelkasten checkerboard keyed|Two-square German field variant", modeName)
        return TwoSquareLetter(letter)

    if V28ModeIn("Four-square Delastelle variant v2", modeName)
        return FourSquareLetter(letter)

    if V28ModeIn("Tri-square ACA classic", modeName)
        return TriSquareLetter(letter)

    if V28ModeIn("Digrafid German field style|Bifid fractionating period 3|Bifid fractionating period 9", modeName)
        return BifidLetter(letter)

    if V28ModeIn("Trifid fractionating period 3|Trifid fractionating period 9", modeName)
        return TrifidFullPeriodLetter(letter)

    if V28ModeIn("Nihilist checkerboard overadd v3", modeName)
        return NihilistLetter(letter)

    if V28ModeIn("ADFGX keyed Polybius field", modeName)
        return KeyedADFGXLetter(letter)

    if V28ModeIn("ADFGVX alphanumeric field v2", modeName)
        return KeyedADFGVXLetter(letter)

    if V28ModeIn("Monome-Dinome French army variant|Straddling checkerboard decimal variant", modeName)
        return MonomeDinomeLetter(letter)

    if V28ModeIn("Polybius torch code Latin|Polybius 6x6 military checkerboard", modeName)
        return V34PolybiusToken(letter)

    if V28ModeIn("Interrupted columnar WWI variant|Myszkowski commercial variant|Double columnar agent variant|Rail fence 6-rail classic|Rail fence 7-rail classic|Turning grille 6x6 Austro-Hungarian|Cardan grille Venetian style|AMSCO period-2 classic|Cadenus ACA variant B|Nihilist columnar transposition style|VIC sequential transposition style|SOE poem transposition v2|Resistance grille code token|Silk code miniature map token", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Gromark keyed primer variant", modeName)
        return GromarkLetter(letter)

    if V28ModeIn("Ragbaby period-word start variant", modeName)
        return RagbabyLetter(letter)

    if V28ModeIn("Nicodemus transposition Vigenere v2", modeName)
        return V28RouteToken(letter)

    if V28ModeIn("Seriated Playfair period 8", modeName)
        return PlayfairLetter(letter)

    if V28ModeIn("Portax ACA variant|Slidefair ACA variant v2", modeName)
        return SlidefairLetter(letter)

    if V28ModeIn("Homophonic nomenclator 1400s|Beale variant book cipher|Navajo code talker word v2|Choctaw code talker token|Q-code maritime token|Z-code military token|Ten-code police radio token|NATO brevity code token v2|ICS flag hoist two-letter|Weather SYNOP code token|Naval signal book token|Army map grid code token|Commercial codebook four-letter|Slater code word variant|Bentley code word variant|ABC code word variant|Zimmermann cable code variant|Diplomatic four-digit book code|Diplomatic five-letter book code|Numbers station Cyrillic style token|OTP subtractive letter groups|OTP additive number groups", modeName)
        return V34CodeToken(letter)

    if V28ModeIn("Dorabella symbol alphabet v2|Freemason pigpen X-grid|Templar pigpen dotted cross|Rosicrucian dotted grid|Zodiac 408 homophonic table v3|Zodiac 340 diagonal read style|Copiale homophonic codebook|Voynich Currier glyph token", modeName)
        return V34SymbolToken(letter)

    if V28ModeIn("Semaphore field flag token|Wigwag single-flag token|American Morse spaced token|International Morse spaced token|Baudot ITA2 figures-letters field|Murray code teleprinter field", modeName)
        return V34SignalToken(letter)

    if V28ModeIn("Vernam Baudot XOR field", modeName)
        return VernamXor5BitLetter(letter)

    if V28ModeIn("Enigma M3 army daily key|Enigma M4 weather key|Enigma Abwehr G style v2|Typex Mark VI style|SIGABA CSP-2900 style|NEMA training key style|Fialka Latin wheel style|KL-7 training key style|Hagelin C-36 pin-lug style|Hagelin CD-57 pocket style v2|Siemens T52ca style|Lorenz SZ42c style|Purple diplomatic 1939 style|Red-Orange Japanese machine style|Rockex II tape style|KW-7 ORESTES stream style", modeName)
        return V28MachineStreamLetter(letter)

    return V34CodeToken(letter)
}

V34CaesarFamily(letter) {
    global modeName, shiftValue
    u := StrUpper(letter)
    if InStr(modeName, "ROT5") {
        ; For letters, ROT5 is represented as a 5-step Caesar transform.
        return ShiftLetter(letter, 5)
    }
    if InStr(modeName, "ROT18")
        return ShiftLetter(letter, 13)
    if InStr(modeName, "ROT25")
        return ShiftLetter(letter, 25)
    return ShiftLetter(letter, shiftValue)
}

V34PolybiusToken(letter) {
    global modeName, keyText
    idx := LetterIndex(StrUpper(letter))
    if InStr(modeName, "6x6") {
        row := Floor(idx / 6) + 1
        col := Mod(idx, 6) + 1
        return row . col . " "
    }
    row := Floor(idx / 5) + 1
    col := Mod(idx, 5) + 1
    if InStr(modeName, "torch")
        return "T" . row . ":" . col . " "
    return row . col . " "
}

V34CodeToken(letter) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    seed := PositiveMod(V28Hash(modeName . keyText . streamIndex), 99999)
    streamIndex += 1
    if InStr(modeName, "four-letter") || InStr(modeName, "Slater") || InStr(modeName, "Bentley") || InStr(modeName, "ABC")
        return SubStr(V31FiveLetterGroup(seed + idx), 1, 4) . " "
    if InStr(modeName, "five-letter")
        return V31FiveLetterGroup(seed + idx) . " "
    if InStr(modeName, "four-digit")
        return V28PadLeft(PositiveMod(seed + idx, 10000), 4, "0") . " "
    if InStr(modeName, "five") || InStr(modeName, "Numbers") || InStr(modeName, "OTP")
        return V28PadLeft(PositiveMod(seed + idx, 100000), 5, "0") . " "
    if InStr(modeName, "Q-code")
        return "Q" . Chr(65 + PositiveMod(idx + seed, 26)) . Chr(65 + PositiveMod(seed, 26)) . " "
    if InStr(modeName, "Z-code")
        return "Z" . Chr(65 + PositiveMod(idx + seed, 26)) . Chr(65 + PositiveMod(seed, 26)) . " "
    if InStr(modeName, "Ten-code")
        return "10-" . V28PadLeft(PositiveMod(seed + idx, 100), 2, "0") . " "
    if InStr(modeName, "Navajo") || InStr(modeName, "Choctaw")
        return V31FiveLetterGroup(seed + idx) . " "
    return V34ShortTag(modeName) . "-" . V28PadLeft(idx, 2, "0") . " "
}

V34SignalToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter)) + 1
    if InStr(modeName, "Morse")
        return MorseLetter(letter)
    if InStr(modeName, "Baudot") || InStr(modeName, "Murray")
        return ToBinaryWidth(idx, 5) . " "
    if InStr(modeName, "Semaphore")
        return "[SEM" . V28PadLeft(idx, 2, "0") . "] "
    if InStr(modeName, "Wigwag")
        return "[WIG" . V28PadLeft(idx, 2, "0") . "] "
    return "[SIG" . V28PadLeft(idx, 2, "0") . "] "
}

V34SymbolToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter))
    if InStr(modeName, "Voynich") {
        eva := ["qo", "ol", "dy", "ai", "in", "ee", "ch", "sh", "or", "ar", "yk", "dal", "ched", "qok", "ot", "ok", "yte", "iin", "qot", "qoky", "olai", "dain", "chey", "sho", "qoke", "otee"]
        return eva[idx + 1] . " "
    }
    if InStr(modeName, "Dorabella") {
        dor := ["◜", "◝", "◞", "◟", "⊂", "⊃", "⊆", "⊇", "⊏", "⊐", "⊓", "⊔", "⋏", "⋎", "⋖", "⋗", "◠", "◡", "◢", "◣", "◤", "◥", "◆", "◇", "○", "●"]
        return dor[idx + 1]
    }
    syms := ["△", "◇", "□", "▽", "○", "◁", "▷", "⬠", "⬡", "⬢", "⬣", "⬤", "✠", "✥", "✦", "✧", "✩", "✪", "✫", "☉", "☽", "☿", "♀", "♂", "♃", "♄"]
    off := PositiveMod(V28Hash(modeName), syms.Length)
    return syms[PositiveMod(idx + off, syms.Length) + 1]
}

V34ShortTag(name) {
    clean := ""
    Loop Parse, name
    {
        ch := A_LoopField
        if ch ~= "^[A-Za-z0-9]$"
            clean .= StrUpper(ch)
    }
    if StrLen(clean) < 4
        clean .= "V34X"
    return SubStr(clean, 1, 4)
}


; ------------------------------------------------------------
; v37 additional real-world / historical cipher adapters
; ------------------------------------------------------------

V37ModeNames() {
    return [
        "Delastelle Bifid 1895 army variant",
        "Delastelle Trifid 1902 army variant",
        "Porta polyalphabetic 1563 variant",
        "Bellaso reciprocal 1555 variant",
        "Vigenere Beaufort reciprocal field",
        "Gronsfeld diplomatic numerals v2",
        "Autokey primer field cipher",
        "Trithemius progressive Latin v2",
        "Diana OTP training sheet v2",
        "St. Cyr slide military v3",
        "Alberti disk movable ring v2",
        "Confederate cipher wheel v3",
        "Union cipher wheel v3",
        "Mexican Army cipher disk",
        "French Army cipher disk 1914",
        "Russian nihilist cipher v2",
        "Checkerboard nihilist overadd",
        "VIC straddling checkerboard v3",
        "VIC chain addition lagged v2",
        "VIC transposition final v2",
        "Doppelkasten Wehrmacht horizontal",
        "Doppelkasten Wehrmacht vertical",
        "Digrafid ACA period 5",
        "Tridigital ACA checkerboard",
        "Tri-square military variant",
        "Seriated Playfair period 10",
        "Playfair naval digraph v2",
        "Double Playfair British variant",
        "Two-square French variant",
        "Four-square army variant",
        "ADFGX fractionation classic",
        "ADFGVX fractionation classic",
        "GEDEFU 36 field checkerboard",
        "Monome-Dinome trench variant",
        "Straddling checkerboard 0-9 classic",
        "Pollux ACA digit map",
        "Morbit ACA digit pairs",
        "Fractionated Morse ACA field variant",
        "Checkerboard transposition period 25",
        "Route cipher spiral military",
        "Route cipher diagonal military",
        "Route cipher boustrophedon military",
        "Rail fence offset military",
        "Redefence cipher ACA",
        "AMSCO German variant",
        "Cadenus 25-row field variant",
        "Swagman transposition ACA",
        "Myszkowski repeated keyword v2",
        "Columnar disrupted field v2",
        "Double columnar SOE variant",
        "UBCHI German double transposition v2",
        "Turning grille Cardan 4x4",
        "Fleissner grille 6x6 v2",
        "Scytale Spartan strip v2",
        "Nomenclator Venetian 1500s",
        "Nomenclator Napoleonic code",
        "Nomenclator Papal cipher",
        "Rossignol syllabic code v3",
        "Louis XIV syllable cipher v3",
        "Great Cipher homophone v3",
        "Beale cipher paper one",
        "Beale cipher paper two",
        "Beale cipher paper three",
        "Zimmermann diplomatic code 13040",
        "Commercial code Lieber code",
        "Commercial code Bentley second phrase",
        "Slater telegraphic code v2",
        "Western Union cable code token",
        "Phillips code press abbreviation",
        "Acme commodity code token",
        "NATO brevity word group",
        "ACP-125 military message token",
        "ACP-131 operating signal token",
        "Q-code aviation token",
        "Z-code naval signal token",
        "Ten-code APCO police token",
        "International Code Signals single flag",
        "International Code Signals two flag",
        "Maritime signal code 1931",
        "Weather SYNOP five figure v2",
        "METAR abbreviation code token",
        "NOTAM abbreviation code token",
        "Grid reference military MGRS token",
        "Map coordinate artillery code",
        "SOE poem code transposition",
        "SOE one-time pad poem token",
        "Resistance silk code token",
        "Numbers station Spanish groups",
        "Numbers station German groups",
        "Numbers station Slavic groups",
        "DRYAD tactical authentication v2",
        "BATCO tactical grid v2",
        "SLIDEX tactical phrase v2",
        "BREVITY airborne codeword token",
        "Enigma M4 officer key live",
        "Enigma M3 Luftwaffe key live",
        "Enigma D commercial key live",
        "Enigma K Swiss key live",
        "Enigma T Tirpitz key live",
        "Typex Mark VIII live",
        "SIGABA CSP-889 rotor live",
        "SIGABA CSP-2900 rotor live v2",
        "Hagelin M-209 lug pattern v2",
        "Hagelin CX-52 pinwheel v2",
        "Hagelin C-446 pocket v2",
        "KL-7 ADONIS rotor live v2",
        "Fialka M-125 Latin live v2",
        "NEMA Swiss rotor 10-wheel v2",
        "Hebern 5-rotor navy live",
        "Kryha machine daily key v3",
        "Purple 6-20 stepping switch v3",
        "Red Japanese diplomatic machine",
        "Orange Japanese naval attache",
        "Lorenz SZ40 chi wheels v2",
        "Lorenz SZ42 psi motor v3",
        "Siemens T52d Geheimschreiber v2",
        "KW-26 ROMULUS stream v2",
        "KW-7 ORESTES stream v2",
        "Rockex OTP teleprinter v2",
        "Vernam teleprinter tape v2",
        "SIGTOT one-time tape style",
        "Fish machine teleprinter token",
        "Dorabella Elgar cipher v2",
        "Gold-Bug Poe substitution v4",
        "Zodiac 408 homophonic v4",
        "Zodiac 340 route homophonic v4",
        "Copiale cipher glyph v2",
        "Voynich EVA Currier B token",
        "Pigpen Freemason dotted v3",
        "Templar cross cipher v3",
        "Rosicrucian cipher grid v4",
        "Malachim occult alphabet v2",
        "Theban witches alphabet v2"
    ]
}

IsV37RealWorldMode(name) {
    for _, item in V37ModeNames() {
        if name = item
            return true
    }
    return false
}

V37RealWorldLetter(letter) {
    global modeName

    if V37ContainsAny(modeName, ["Bifid", "Delastelle Bifid"])
        return BifidLetter(letter)

    if V37ContainsAny(modeName, ["Trifid", "Delastelle Trifid"])
        return TrifidCoordinateLetter(letter)

    if V37ContainsAny(modeName, ["Playfair", "Doppelkasten", "Two-square", "Four-square", "Seriated Playfair"])
        return PlayfairLetter(letter)

    if V37ContainsAny(modeName, ["ADFGX", "ADFGVX", "GEDEFU", "Polybius", "Checkerboard", "Monome", "Straddling", "Tridigital", "Nihilist"])
        return V37PolybiusStyleToken(letter)

    if V37ContainsAny(modeName, ["Morse", "Pollux", "Morbit", "Fractionated Morse", "Semaphore", "Wigwag", "Baudot", "Murray", "Vernam teleprinter", "Vernam"])
        return V37SignalStyleToken(letter)

    if V37ContainsAny(modeName, ["Enigma", "Typex", "SIGABA", "Hagelin", "KL-7", "Fialka", "NEMA", "Hebern", "Kryha", "Purple", "Red Japanese", "Orange Japanese", "Lorenz", "Siemens", "KW-", "Rockex", "SIGTOT", "Fish machine"])
        return V37MachineStyleLetter(letter)

    if V37ContainsAny(modeName, ["Dorabella", "Gold-Bug", "Zodiac", "Copiale", "Voynich", "Pigpen", "Templar", "Rosicrucian", "Malachim", "Theban"])
        return V37SymbolStyleToken(letter)

    if V37ContainsAny(modeName, ["Nomenclator", "Rossignol", "Louis XIV", "Great Cipher", "Beale", "Zimmermann", "Commercial", "Slater", "Western Union", "Phillips code", "Acme", "NATO", "ACP-", "Q-code", "Z-code", "Ten-code", "International Code", "Maritime", "Weather", "METAR", "NOTAM", "Grid", "Map", "SOE", "Resistance", "Numbers station", "DRYAD", "BATCO", "SLIDEX", "BREVITY"])
        return V37CodebookStyleToken(letter)

    if V37ContainsAny(modeName, ["Route", "Rail", "Redefence", "AMSCO", "Cadenus", "Swagman", "Myszkowski", "Columnar", "UBCHI", "grille", "Fleissner", "Scytale", "Turning grille"])
        return V37TranspositionStyleToken(letter)

    return V37PolyalphabeticStyleLetter(letter)
}

V37ContainsAny(haystack, needles) {
    for _, needle in needles {
        if InStr(haystack, needle)
            return true
    }
    return false
}

V37PolyalphabeticStyleLetter(letter) {
    global modeName, keyText, shiftValue, streamIndex
    u := StrUpper(letter)
    idx := LetterIndex(u)
    keyShift := KeyShiftAt(keyText, streamIndex)
    variant := PositiveMod(V28Hash(modeName), 26)
    streamIndex += 1

    if InStr(modeName, "Beaufort")
        outIdx := PositiveMod((keyShift + variant) - idx, 26)
    else if InStr(modeName, "Gronsfeld")
        outIdx := PositiveMod(idx + DigitShiftAt(keyText, streamIndex - 1) + variant, 26)
    else if InStr(modeName, "Diana")
        outIdx := PositiveMod(25 - (idx + keyShift + variant), 26)
    else if InStr(modeName, "Alberti") || InStr(modeName, "disk") || InStr(modeName, "wheel") || InStr(modeName, "slide")
        outIdx := PositiveMod(idx + shiftValue + variant + Floor((streamIndex - 1) / 5), 26)
    else
        outIdx := PositiveMod(idx + keyShift + variant, 26)

    out := Chr(65 + outIdx)
    return letter ~= "^[a-z]$" ? StrLower(out) : out
}

V37PolybiusStyleToken(letter) {
    global modeName, keyText, streamIndex
    u := StrUpper(letter)
    idx := LetterIndex(u)
    variant := PositiveMod(V28Hash(modeName . keyText), 36)
    streamIndex += 1

    if InStr(modeName, "ADFGVX") || InStr(modeName, "GEDEFU") {
        labels := InStr(modeName, "GEDEFU") ? "GEDEFU" : "ADFGVX"
        n := PositiveMod(idx + variant, 36)
        return SubStr(labels, Floor(n / 6) + 1, 1) . SubStr(labels, Mod(n, 6) + 1, 1) . " "
    }

    if InStr(modeName, "ADFGX") {
        labels := "ADFGX"
        n := PositiveMod(idx + variant, 25)
        return SubStr(labels, Floor(n / 5) + 1, 1) . SubStr(labels, Mod(n, 5) + 1, 1) . " "
    }

    if InStr(modeName, "Nihilist") {
        n := PositiveMod(idx + variant, 25)
        return (Floor(n / 5) + 1) . (Mod(n, 5) + 1 + 10) . " "
    }

    n := PositiveMod(idx + variant, 25)
    return (Floor(n / 5) + 1) . (Mod(n, 5) + 1) . " "
}

V37SignalStyleToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter)) + 1
    if InStr(modeName, "Morse") || InStr(modeName, "Pollux") || InStr(modeName, "Morbit")
        return MorseLetter(letter)
    if InStr(modeName, "Baudot") || InStr(modeName, "Murray") || InStr(modeName, "Vernam")
        return ToBinaryWidth(idx - 1, 5) . " "
    if InStr(modeName, "Semaphore")
        return "[SEM" . V28PadLeft(idx, 2, "0") . "] "
    if InStr(modeName, "Wigwag")
        return "[WIG" . V28PadLeft(idx, 2, "0") . "] "
    return "[SIG" . V28PadLeft(idx, 2, "0") . "] "
}

V37MachineStyleLetter(letter) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter))
    seed := V28Hash(modeName . keyText . streamIndex)
    step := PositiveMod(seed + (streamIndex * 7), 26)
    streamIndex += 1
    out := Chr(65 + PositiveMod(idx + step, 26))
    return letter ~= "^[a-z]$" ? StrLower(out) : out
}

V37CodebookStyleToken(letter) {
    global modeName, keyText, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    seed := PositiveMod(V28Hash(modeName . keyText . streamIndex), 99999)
    streamIndex += 1
    if InStr(modeName, "Q-code")
        return "Q" . Chr(65 + PositiveMod(seed + idx, 26)) . Chr(65 + PositiveMod(Floor(seed / 3), 26)) . " "
    if InStr(modeName, "Z-code")
        return "Z" . Chr(65 + PositiveMod(seed + idx, 26)) . Chr(65 + PositiveMod(Floor(seed / 5), 26)) . " "
    if InStr(modeName, "Ten-code")
        return "10-" . V28PadLeft(PositiveMod(seed + idx, 100), 2, "0") . " "
    if InStr(modeName, "five figure") || InStr(modeName, "Numbers") || InStr(modeName, "DRYAD") || InStr(modeName, "BATCO")
        return V28PadLeft(PositiveMod(seed + idx, 100000), 5, "0") . " "
    if InStr(modeName, "four") || InStr(modeName, "ACP")
        return SubStr(V31FiveLetterGroup(seed + idx), 1, 4) . " "
    return V31FiveLetterGroup(seed + idx) . " "
}

V37TranspositionStyleToken(letter) {
    global modeName, streamIndex
    idx := LetterIndex(StrUpper(letter)) + 1
    streamIndex += 1
    return "[" . V34ShortTag(modeName) . V28PadLeft(streamIndex, 2, "0") . ":" . V28PadLeft(idx, 2, "0") . "]"
}

V37SymbolStyleToken(letter) {
    global modeName
    idx := LetterIndex(StrUpper(letter))
    if InStr(modeName, "Voynich") {
        eva := ["qo", "ol", "dy", "ai", "in", "ee", "ch", "sh", "or", "ar", "yk", "dal", "ched", "qok", "ot", "ok", "yte", "iin", "qot", "qoky", "olai", "dain", "chey", "sho", "qoke", "otee"]
        return eva[idx + 1] . " "
    }
    if InStr(modeName, "Dorabella") {
        dor := ["◜", "◝", "◞", "◟", "⊂", "⊃", "⊆", "⊇", "⊏", "⊐", "⊓", "⊔", "⋏", "⋎", "⋖", "⋗", "◠", "◡", "◢", "◣", "◤", "◥", "◆", "◇", "○", "●"]
        return dor[idx + 1]
    }
    if InStr(modeName, "Gold-Bug") {
        gold := ["5", "2", "-", ")", "6", "*", ";", "4", "8", "1", "0", "9", "†", "‡", ".", "$", "?", "¶", "]", "[", "§", "!", "&", "<", ">", "="]
        return gold[idx + 1]
    }
    syms := ["△", "◇", "□", "▽", "○", "◁", "▷", "⬠", "⬡", "⬢", "⬣", "⬤", "✠", "✥", "✦", "✧", "✩", "✪", "✫", "☉", "☽", "☿", "♀", "♂", "♃", "♄"]
    off := PositiveMod(V28Hash(modeName), syms.Length)
    return syms[PositiveMod(idx + off, syms.Length) + 1]
}


; ------------------------------------------------------------
; v38 additional real-world / historical cipher adapters
; ------------------------------------------------------------

V38ModeNames() {
    return [
        "Aeneas tactical disk variant",
        "Polybius fire-signal square",
        "Polybius prisoners square",
        "Caesar legion field shift",
        "Augustus Caesar shift variant",
        "ROT5 digit companion classic",
        "ROT18 alphanumeric classic v2",
        "ROT47 teletype printable v2",
        "Atbash biblical Hebrew style v2",
        "Affine Caesar 5x plus 8 classic",
        "Affine Decimation 7 classic",
        "Affine Decimation 11 classic",
        "Keyword alphabet K1 ACA",
        "Keyword alphabet K2 ACA",
        "Keyword alphabet K3 ACA",
        "Keyword alphabet K4 ACA",
        "Aristocrat K1 simple substitution",
        "Aristocrat K2 simple substitution",
        "Patristocrat K1 no-space substitution",
        "Patristocrat K2 no-space substitution",
        "Homophonic frequency table 1700s",
        "Homophonic syllabary 1600s",
        "Nomenclator Mary Queen of Scots",
        "Nomenclator Elizabethan court",
        "Nomenclator Spanish court 1600s",
        "Nomenclator Venetian envoy v2",
        "Papal nomenclator Vatican style",
        "French diplomatic nomenclator 1700",
        "Napoleonic Grand Chiffre style",
        "Rossignol homophone table v4",
        "Louis XIV diplomatic syllables v4",
        "Great Cipher nulls and syllables",
        "Beale book cipher Declaration v3",
        "Declaration book cipher 1776 style",
        "Bible book cipher chapter verse",
        "Commercial code 5-letter groups v2",
        "Commercial code 5-number groups v2",
        "Bentley complete phrase code token",
        "ABC telegraph code phrase v2",
        "Acme commodity phrase code v2",
        "Slater code 1870 phrase v2",
        "Lieber code diplomatic token",
        "Zimmermann Telegram codebook v2",
        "M-94 Army wheel daily offset",
        "Jefferson wheel random disk order",
        "Bazeries cylinder numeric key v2",
        "Wheatstone cryptograph alphabet v2",
        "St Cyr slide officer key",
        "Confederate signal disk 1860s",
        "Union route disk 1860s",
        "Mexican cipher disk 1916 variant",
        "Alberti disk periodic switch v3",
        "Alberti disk plaintext indicator",
        "Bellaso reciprocal alphabet 1564",
        "Bellaso countersign long key",
        "Vigenere autoclave Beaufort style",
        "Vigenere running key newspaper",
        "Vigenere tabula recta Latin v2",
        "Babbage progressive key Vigenere",
        "Kasiski repeated-key Vigenere",
        "Gronsfeld numeric primer v3",
        "Diana reciprocal OTP sheet v3",
        "Trithemius Ave Maria table v2",
        "Trithemius Polygraphia codeword v2",
        "Porta table 13 alphabets v2",
        "Porta reciprocal field table",
        "Porta wheel alphabet v2",
        "Beaufort Admiralty reciprocal v2",
        "Variant Beaufort military key v2",
        "Beaufort autoclave field v2",
        "Progressive key ACA v2",
        "Interrupted key ACA v2",
        "Quagmire I mixed alphabet ACA v2",
        "Quagmire II mixed alphabet ACA v2",
        "Quagmire III mixed alphabet ACA v2",
        "Quagmire IV mixed alphabet ACA v2",
        "Gromark primer transposition ACA v2",
        "Ragbaby periodic key ACA v2",
        "Cadenus alphabetic transposition v2",
        "AMSCO irregular transposition v2",
        "Myszkowski transposition ACA v3",
        "Swagman route transposition v2",
        "Redefence rail cipher v2",
        "Rail fence offset 3 rail v2",
        "Rail fence zigzag railway v2",
        "Scytale Greek staff v3",
        "Columnar transposition incomplete v2",
        "Columnar transposition complete v2",
        "Double columnar French resistance",
        "Double columnar German army v3",
        "UBCHI ADFGX double columnar",
        "Route cipher spiral clockwise v2",
        "Route cipher inward spiral v2",
        "Route cipher outward spiral v2",
        "Cardan grille literary mask",
        "Cardan grille diplomatic 6x6",
        "Fleissner turning grille 8x8",
        "Turning grille four-rotation v2",
        "Checkerboard transposition ACA v2",
        "Playfair Lord Playfair 1854 v2",
        "Playfair British field manual v2",
        "Playfair German 6x6 field v2",
        "Playfair naval bigram key v3",
        "Double Playfair Wehrmacht v2",
        "Doppelkasten German horizontal v3",
        "Doppelkasten German vertical v3",
        "Two-square French army v2",
        "Four-square Delastelle army v2",
        "Tri-square ACA period v2",
        "Digrafid fractionated digraph v2",
        "Bifid Delastelle period 5 v3",
        "Bifid Delastelle period 7 v2",
        "Trifid Delastelle period 5 v3",
        "Trifid Delastelle period 7 v2",
        "Nihilist substitution overadd v4",
        "Nihilist transposition checkerboard v2",
        "Russian Nihilist prison code v3",
        "Straddling checkerboard VIC v4",
        "Monome-Dinome checkerboard v2",
        "Pollux Morse digit cipher v2",
        "Morbit Morse pair cipher v2",
        "Fractionated Morse ACA v3",
        "ADFGX German Army 1918 v3",
        "ADFGVX German Army 1918 v3",
        "ADFGX Nebel field square v2",
        "ADFGVX Nebel alphanumeric v2",
        "GEDEFU German field cipher v2",
        "Grandpre checkerboard ACA v2",
        "Phillips cipher sliding square v2",
        "Phillips RC variant ACA v2",
        "Seriated Playfair ACA period v2",
        "Seriated Bifid ACA period v2",
        "CM Bifid ACA variant v2",
        "Tridigital ACA field cipher v2",
        "VIC sequential transposition v2",
        "VIC lagged Fibonacci addition v2",
        "VIC personal number key v2",
        "VIC agent checkerboard v4",
        "VIC disrupted transposition v2",
        "M-209 lug cage Army v3",
        "M-209 pinwheel field v3",
        "Hagelin B-21 pinwheel style",
        "Hagelin C-36 Swedish style v2",
        "Hagelin C-38 converter style",
        "Hagelin C-52 lug cage v3",
        "Hagelin CX-52 advanced v3",
        "Hagelin CD-57 pocket v3",
        "Enigma I army key sheet v2",
        "Enigma M3 naval bigram key",
        "Enigma M4 Triton weather key",
        "Enigma M4 U-boat Kurzsignal",
        "Enigma G Abwehr key v3",
        "Enigma K Swiss railway v2",
        "Enigma T Tirpitz naval v2",
        "Enigma D commercial export v2",
        "Typex Mark II plugboard v2",
        "Typex Mark VI rotor order v2",
        "Typex Mark VIII rotor style v2",
        "SIGABA CSP-889 stepping v2",
        "SIGABA CSP-2900 stepping v3",
        "NEMA Swiss 10-wheel army v3",
        "Fialka M-125 Cyrillic live v2",
        "Fialka M-125 Latin training v3",
        "KL-7 ADONIS military key v3",
        "Hebern electric rotor five-wheel",
        "Hebern single rotor 1920s v2",
        "Kryha Standard pocket machine v2",
        "Purple diplomatic switchboard v4",
        "Japanese Red machine v2",
        "Japanese Orange attaché machine v2",
        "Lorenz SZ40 chi wheel v3",
        "Lorenz SZ42 psi wheel v4",
        "Lorenz SZ42 motor wheel v2",
        "Siemens T52a Sturgeon v2",
        "Siemens T52d Sturgeon v3",
        "Siemens T52e Sturgeon v2",
        "KW-26 ROMULUS teleprinter v3",
        "KW-7 ORESTES teleprinter v3",
        "Rockex II one-time tape v2",
        "SIGTOT one-time tape v2",
        "Vernam one-time teleprinter tape v3",
        "Soviet one-time pad five-letter",
        "Soviet one-time pad five-digit",
        "DRYAD numeral authentication v3",
        "BATCO tactical code grid v3",
        "SLIDEX tactical phrase board v3",
        "NATO brevity codeword v2",
        "ACP-125 radiotelephone code v2",
        "ACP-131 operating signal v2",
        "Q-code maritime aviation v2",
        "Z-code naval operating signal v2",
        "Ten-code APCO police v2",
        "International Code of Signals 1965",
        "International maritime flag hoist v2",
        "Popham flag telegraph naval",
        "Chappe optical telegraph French v2",
        "Wigwag signal flag Myer code",
        "Semaphore flag naval v2",
        "Baudot ITA2 teleprinter v2",
        "Murray code teleprinter v2",
        "Vernam Baudot XOR tape v2",
        "Morse American railroad v2",
        "Morse International 1865 v2",
        "Wabun Japanese Morse token",
        "Numbers station Czech groups",
        "Numbers station Russian groups v2",
        "Numbers station English groups v2",
        "Numbers station one-time pad token",
        "SOE poem code field v3",
        "SOE silk code map v2",
        "Resistance handkerchief code v2",
        "Poem code transposition SOE v2",
        "Book cipher page-line-letter v2",
        "Dorabella Elgar symbol set v3",
        "Gold-Bug Poe exact-symbol style",
        "Zodiac 408 homophonic style v5",
        "Zodiac 340 transposition style v5",
        "Copiale glyph cluster style v3",
        "Voynich EVA Currier A token",
        "Voynich EVA Currier B token v2"
    ]
}

IsV38RealWorldMode(name) {
    for _, item in V38ModeNames() {
        if name = item
            return true
    }
    return false
}

V38RealWorldLetter(letter) {
    global modeName

    ; Keep v38 stable by routing all new historical labels through existing,
    ; self-check-safe live adapters. These are live-typing approximations for
    ; systems that normally need blocks, codebooks, rotors, wheels, or pads.
    if V37ContainsAny(modeName, ["ADFGX", "ADFGVX", "GEDEFU", "Polybius", "Checkerboard", "Monome", "Straddling", "Tridigital", "Grandpre", "Nihilist", "VIC"])
        return V37PolybiusStyleToken(letter)

    if V37ContainsAny(modeName, ["Morse", "Pollux", "Morbit", "Fractionated Morse", "Semaphore", "Wigwag", "Baudot", "Murray", "Vernam", "teleprinter", "flag", "Chappe", "Popham", "Wabun"])
        return V37SignalStyleToken(letter)

    if V37ContainsAny(modeName, ["Enigma", "Typex", "SIGABA", "Hagelin", "KL-7", "Fialka", "NEMA", "Hebern", "Kryha", "Purple", "Japanese", "Lorenz", "Siemens", "KW-", "Rockex", "SIGTOT", "M-209"])
        return V37MachineStyleLetter(letter)

    if V37ContainsAny(modeName, ["Dorabella", "Gold-Bug", "Zodiac", "Copiale", "Voynich", "Pigpen", "Templar", "Rosicrucian", "Malachim", "Theban"])
        return V37SymbolStyleToken(letter)

    if V37ContainsAny(modeName, ["Nomenclator", "Rossignol", "Louis XIV", "Great Cipher", "Beale", "Zimmermann", "Commercial", "Bentley", "ABC", "Acme", "Slater", "Lieber", "Code", "code", "NATO", "ACP-", "Q-code", "Z-code", "Ten-code", "International", "Maritime", "Weather", "METAR", "NOTAM", "Grid", "Map", "SOE", "Resistance", "Numbers station", "DRYAD", "BATCO", "SLIDEX", "BREVITY", "Bible", "Dictionary", "Book"])
        return V37CodebookStyleToken(letter)

    if V37ContainsAny(modeName, ["Route", "Rail", "Redefence", "AMSCO", "Cadenus", "Swagman", "Myszkowski", "Columnar", "UBCHI", "grille", "Fleissner", "Scytale", "Turning grille", "transposition", "Transposition", "Cardan"])
        return V37TranspositionStyleToken(letter)

    if V37ContainsAny(modeName, ["Playfair", "Doppelkasten", "Two-square", "Four-square", "Tri-square", "Digrafid", "Seriated Playfair"])
        return PlayfairLetter(letter)

    if V37ContainsAny(modeName, ["Bifid", "Trifid", "Delastelle"])
        return V37PolybiusStyleToken(letter)

    return V37PolyalphabeticStyleLetter(letter)
}


; ------------------------------------------------------------
; v39 additional real-world / historical cipher adapters
; ------------------------------------------------------------

V39ModeNames() {
    return [
        "Mlecchita Vikalpa substitution",
        "Kautiliya secret writing style",
        "Arthashastra cipher wheel style",
        "Ancient Indian Kutalipi token",
        "Hebrew Atbash original alphabet",
        "Hebrew Albam substitution",
        "Hebrew Atbah substitution",
        "Greek Skytale military dispatch",
        "Greek Polybius torch two-square",
        "Greek Polybius naval beacon",
        "Roman Caesar military watchword",
        "Roman Caesar dispatch shift II",
        "Roman Caesar dispatch shift IV",
        "Roman Caesar dispatch shift VI",
        "Augustus cipher no-A shift",
        "Tironian note token cipher",
        "Monastic manuscript cipher token",
        "Ogham cryptic scoreline cipher",
        "Runic substitution medieval elder",
        "Runic substitution younger futhark",
        "Runic Caesar stave shift",
        "Templar cross cipher alphabet",
        "Templar banking cipher token",
        "Cistercian monk numeral cipher",
        "Cistercian numeral letter code",
        "Masonic pigpen prison variant",
        "Freemason pigpen dot variant",
        "Rosicrucian nine-chamber cipher",
        "Cornelius Agrippa Theban cipher",
        "Trithemius Steganographia spirit names",
        "Trithemius Polygraphia Ave Maria v3",
        "Trithemius progressive alphabet 1518",
        "Alberti disk lowercase ring v3",
        "Alberti disk index letter system",
        "Alberti disk moving index every four",
        "Bellaso reciprocal table 1553 v2",
        "Bellaso countersign reciprocal v4",
        "Porta cipher table Naples 1563",
        "Porta polyalphabetic reciprocal v3",
        "Della Porta natural magic disk v2",
        "Vigenere autokey 1586 original",
        "Vigenere repeated key 19th century v2",
        "Vigenere tabula recta diplomatic v3",
        "Beaufort naval reciprocal 1857 v3",
        "Wheatstone cryptograph disk v3",
        "Wheatstone Playfair digraph 1854",
        "Lyon Playfair variant field",
        "Playfair Boer War field cipher",
        "Playfair WWI trench cipher",
        "Playfair WWII Australian field",
        "Playfair German army 6x6 v3",
        "Double Playfair German worksheet",
        "Doppelkasten Wehrmacht field v4",
        "Two-square French diplomatic v3",
        "Four-square Delastelle 1902 v3",
        "Bifid Delastelle 1895 period 6",
        "Bifid Delastelle no-period classic",
        "Trifid Delastelle 1901 period 6",
        "Trifid Delastelle no-period classic",
        "Nihilist Russian numbers 1880",
        "Nihilist substitution prison v4",
        "Nihilist transposition Siberian v3",
        "Vigenere Beaufort hybrid ACA",
        "Gronsfeld Bavarian diplomatic v3",
        "Gronsfeld count key worksheet",
        "Gromark ACA primer transposition v3",
        "Ragbaby ACA word-position v3",
        "Nicodemus ACA transposition v3",
        "Portax ACA digraph cipher",
        "Quagmire I keyed indicator v3",
        "Quagmire II keyed indicator v3",
        "Quagmire III keyed indicator v3",
        "Quagmire IV keyed indicator v3",
        "Progressive key cipher ACA v3",
        "Interrupted key cipher ACA v3",
        "Kasiski Vigenere training cipher v2",
        "Babbage autokey cryptanalysis sample",
        "Aristocrat K3 simple substitution",
        "Aristocrat K4 simple substitution",
        "Patristocrat K3 no-space substitution",
        "Patristocrat K4 no-space substitution",
        "Homophonic Spanish court cipher",
        "Homophonic French court cipher",
        "Homophonic Papal cipher 1600s",
        "Homophonic Zodiac style table v6",
        "Nomenclator Renaissance envoy",
        "Nomenclator Thirty Years War",
        "Nomenclator Habsburg court",
        "Nomenclator Bourbon court",
        "Nomenclator Stuart court",
        "Rossignol Great Cipher table v5",
        "Louis XIV syllabary table v5",
        "Napoleonic diplomatic codebook v2",
        "Confederate Vigenere disk v2",
        "Confederate route cipher dispatch",
        "Union Army cipher disk v2",
        "Federal cipher disk Civil War",
        "Mexican Army cipher disk 1916 v2",
        "Prussian field cipher disk",
        "Austro-Hungarian cipher disk",
        "Russian diplomatic chiffre 1800",
        "Ottoman diplomatic code token",
        "Zimmermann code 13040 variant v2",
        "World War I trench code word",
        "German trench codebook token",
        "French trench codebook token",
        "British trench codebook token",
        "ADFGX Nebel 1918 worksheet",
        "ADFGVX Nebel 1918 worksheet",
        "ADFGX columnar transposition v4",
        "ADFGVX six-symbol field v4",
        "GEDEFU German checkerboard v3",
        "UBCHI pre-ADFGX transposition v3",
        "Monome-Dinome trench checkerboard v3",
        "Straddling checkerboard spy v5",
        "VIC checkerboard five-line v5",
        "VIC chain addition lagged v4",
        "VIC personal date key v3",
        "VIC disrupted transposition v3",
        "VIC sequential transposition v3",
        "DRYAD tactical numeral sheet v4",
        "BATCO authentication table v4",
        "SLIDEX battlefield phrase v4",
        "SOE poem transposition v4",
        "SOE silk one-time pad map v3",
        "Resistance book cipher v3",
        "Spy pencil cipher field v2",
        "Poem code agent variant v3",
        "Book cipher Bible KJV v2",
        "Book cipher dictionary page word",
        "Beale cipher pamphlet v4",
        "Dorabella cipher arc token v4",
        "Gold-Bug Poe symbol token v4",
        "Copiale manuscript glyph v4",
        "Voynich EVA botanical page token",
        "Voynich EVA astronomical page token",
        "Mary Stuart symbol nomenclator v2",
        "Elizabeth I court cipher v2",
        "Babington plot cipher token",
        "Cardan grille 1550 mask v2",
        "Cardano grille letter mask v2",
        "Fleissner grille WWI 6x6 v3",
        "Turning grille diplomatic square v3",
        "Route cipher Hindenburg trench",
        "Columnar transposition WWI army",
        "Double columnar resistance v4",
        "Myszkowski repeated keyword v4",
        "AMSCO transposition ACA v3",
        "Cadenus ACA alphabetic v3",
        "Swagman route ACA v3",
        "Rail fence telegraph v3",
        "Redefence rail offset v3",
        "Scytale parchment strip v4",
        "Jefferson wheel 36-disk v2",
        "Jefferson-Bazeries wheel v3",
        "M-94 Army cylinder 25 wheel v3",
        "M-138-A strip cipher v2",
        "Bazeries cylinder 20 disk v3",
        "Hebern rotor five-wheel v3",
        "Hebern electric code machine v3",
        "Kryha Liliput pocket cipher",
        "Kryha Standard disk 1924 v3",
        "Enigma I Luftwaffe key v3",
        "Enigma I Heer key v3",
        "Enigma M3 Kriegsmarine key v3",
        "Enigma M4 Triton Shark v3",
        "Enigma Uhr switch board v2",
        "Enigma Kenngruppenbuch token",
        "Enigma Kurzsignalheft token",
        "Enigma weather short signal v2",
        "Enigma Abwehr G312 style",
        "Swiss K commercial Enigma v3",
        "Railway Enigma Rocket v2",
        "Tirpitz Enigma K variant v3",
        "Typex Mark 22 style",
        "Typex reflector plugboard style",
        "SIGABA CSP-888 style",
        "SIGABA index rotor style v2",
        "NEMA army training key v4",
        "Fialka M-125 30-wheel v3",
        "KL-7 ADONIS daily key v4",
        "Hagelin C-35 lug style",
        "Hagelin C-446 pocket style",
        "Hagelin CX-52 irregular motion v4",
        "Hagelin M-209 pin cage v4",
        "Hagelin BC-38 Swedish field",
        "Lorenz SZ40/42 chi stream v4",
        "Lorenz SZ42 psi mu stream v5",
        "Siemens T52 Geheimschreiber v4",
        "Siemens T43 one-time tape v2",
        "Soviet Fialka Cyrillic v4",
        "Soviet VIC pencil-and-paper v6",
        "Soviet OTP five-figure pad v2",
        "Soviet one-time letter pad v3",
        "Purple Japanese diplomatic v5",
        "Japanese Red attaché machine v3",
        "Japanese Coral cipher machine style",
        "Japanese Jade machine style token",
        "Japanese naval code JN-25 token",
        "Japanese army codebook token",
        "British Naval Cypher No 3 token",
        "British Government Code token",
        "US Army SIGTOT tape v3",
        "Rockex one-time tape v4",
        "KW-26 online rotor stream v4",
        "KW-7 ORESTES line cipher v4",
        "HY-2 voice scrambler token",
        "STU-I secure voice token",
        "Morse Continental field code v3",
        "American Morse railroad sounder v3",
        "Wabun Japanese Morse v2",
        "Baudot ITA1 telegraph v2",
        "Baudot ITA2 figure shift v3",
        "Murray teleprinter code v3",
        "Vernam Baudot 1917 v3",
        "Wigwag Myer army signal v2",
        "Chappe semaphore arm positions v3",
        "Popham naval flag code v2",
        "Marryat signal code token",
        "International Code of Signals 1931",
        "International Code of Signals 1969 v2",
        "Q-code radiotelegraph v3",
        "Z-code naval signal v3",
        "ACP-124 radiotelegraph code",
        "ACP-131 operating signal v3",
        "Brevity code NATO tactical v3",
        "Ten-code APCO public safety v3",
        "Phillips press code telegraph v2",
        "Western Union 92 code token",
        "Bentley second phrase code token",
        "ABC 5th edition telegraph code",
        "Lieber field code 1915 token"
    ]
}

IsV39RealWorldMode(name) {
    for _, item in V39ModeNames() {
        if name = item
            return true
    }
    return false
}

V39RealWorldLetter(letter) {
    global modeName

    ; v39 names are routed through existing stable live adapters. These are
    ; intended as visible local typing transformations, not exact simulators
    ; for systems that historically required wheels, pads, codebooks, or blocks.
    if V37ContainsAny(modeName, ["ADFGX", "ADFGVX", "GEDEFU", "Polybius", "Checkerboard", "Monome", "Straddling", "Grandpre", "Nihilist", "VIC", "DRYAD", "BATCO", "SLIDEX", "Q-code", "Z-code", "ACP-", "Brevity", "Ten-code"])
        return V37PolybiusStyleToken(letter)

    if V37ContainsAny(modeName, ["Morse", "Baudot", "Murray", "Vernam", "Wigwag", "Chappe", "Popham", "Marryat", "Semaphore", "Signal", "flag", "telegraph", "teleprinter", "sounder", "Wabun"])
        return V37SignalStyleToken(letter)

    if V37ContainsAny(modeName, ["Enigma", "Typex", "SIGABA", "NEMA", "Fialka", "KL-7", "Hagelin", "Hebern", "Kryha", "Lorenz", "Siemens", "Purple", "Japanese", "Rockex", "KW-", "SIGTOT", "HY-", "STU-", "M-209", "M-94", "M-138", "Jefferson", "Bazeries"])
        return V37MachineStyleLetter(letter)

    if V37ContainsAny(modeName, ["Dorabella", "Gold-Bug", "Copiale", "Voynich", "Ogham", "Runic", "Templar", "Masonic", "Freemason", "Rosicrucian", "Theban", "Cistercian", "Tironian", "symbol", "glyph"])
        return V37SymbolStyleToken(letter)

    if V37ContainsAny(modeName, ["Nomenclator", "Rossignol", "Louis XIV", "Great Cipher", "Beale", "Zimmermann", "Code", "code", "codebook", "phrase", "Dictionary", "Book", "Bible", "Mary", "Elizabeth", "Babington", "NATO", "Western Union", "Bentley", "ABC", "Lieber"])
        return V37CodebookStyleToken(letter)

    if V37ContainsAny(modeName, ["Route", "Rail", "Redefence", "AMSCO", "Cadenus", "Swagman", "Myszkowski", "Columnar", "UBCHI", "grille", "Grille", "Fleissner", "Scytale", "Cardan", "Cardano", "transposition", "Transposition"])
        return V37TranspositionStyleToken(letter)

    if V37ContainsAny(modeName, ["Playfair", "Doppelkasten", "Two-square", "Four-square", "Bifid", "Trifid", "Delastelle", "Digrafid", "Portax"])
        return V37PolybiusStyleToken(letter)

    return V37PolyalphabeticStyleLetter(letter)
}

; ------------------------------------------------------------
; v40 additional real-world / historical cipher adapters
; ------------------------------------------------------------

V40ModeNames() {
    return [
        "Aeneas siege disk variant",
        "Aeneas fire-signal alphabet",
        "Polybius checkerboard military v5",
        "Polybius torch relay token v2",
        "Spartan scytale courier strip v5",
        "Caesar Gallic War shift v2",
        "Caesar alphabet wrap field v3",
        "Augustus cipher variant v2",
        "ROT5 telegraph numeric classic",
        "ROT18 Usenet classic v2",
        "ROT47 teleprinter printable v2",
        "Atbash Hebrew square script v2",
        "Albam Hebrew reciprocal v2",
        "Atbah Hebrew substitution v2",
        "Temurah cipher token",
        "Gematria number cipher token",
        "Kabbalistic notarikon token",
        "Ogham edge-notch cipher v2",
        "Ogham stemline secret marks",
        "Elder Futhark rune cipher v2",
        "Younger Futhark rune cipher v2",
        "Runic Caesar wheel v2",
        "Rök runestone shift style",
        "Templar cross alphabet v2",
        "Freemason pigpen grid v3",
        "Masonic tic-tac-toe pigpen",
        "Rosicrucian pigpen variant v3",
        "Theban alphabet Agrippa v2",
        "Malachim alphabet Agrippa v2",
        "Celestial alphabet Agrippa v2",
        "Enochian alphabet Dee token v2",
        "Bacon biliteral original 24-letter",
        "Bacon biliteral modern 26-letter",
        "Bacon italic-roman stego token",
        "Trithemius tabula recta 1508 v2",
        "Trithemius progressive cipher v4",
        "Trithemius Ave Maria covertext v4",
        "Porta digraph table 1563 v2",
        "Porta keyword table classic v2",
        "Porta disk reciprocal v4",
        "Bellaso la cifra del Sig Giovan v2",
        "Bellaso reciprocal countersign v5",
        "Bellaso autokey countersign style",
        "Alberti disk fixed index v4",
        "Alberti disk progressive index v4",
        "Alberti numeric shift indicator v2",
        "Saint-Cyr military slide v4",
        "Saint-Cyr French army disk v2",
        "Della Porta cipher disk v3",
        "Vigenere chiffre indechiffrable v2",
        "Vigenere autokey original v4",
        "Vigenere running-key field v3",
        "Vigenere Beaufort reciprocal mix v2",
        "Babbage autokey sample v2",
        "Kasiski repeated-key sample v3",
        "Beaufort Royal Navy table v4",
        "Beaufort Admiralty cipher v3",
        "Variant Beaufort reciprocal field",
        "Gronsfeld count numeral key v4",
        "Gronsfeld decimal field key v3",
        "Diana cryptosystem OTP v3",
        "Diana reciprocal pad worksheet",
        "Quagmire I ACA standard v4",
        "Quagmire II ACA standard v4",
        "Quagmire III ACA standard v4",
        "Quagmire IV ACA standard v4",
        "Quagmire I K1-K2 indicator",
        "Quagmire II K1-K2 indicator",
        "Quagmire III K1-K2 indicator",
        "Quagmire IV K1-K2 indicator",
        "Gromark primer chain v4",
        "Gromark mixed alphabet v4",
        "Ragbaby word-position classic v4",
        "Ragbaby keyed alphabet v2",
        "Nicodemus columnar Vigenere v4",
        "Nicodemus ACA cipher v4",
        "Phillips sliding square v4",
        "Phillips RC sliding square v3",
        "Portax digraph ACA v2",
        "Portax slide cipher v2",
        "Digrafid cipher ACA v3",
        "Tridigital cipher ACA v3",
        "Cadenus alphabetic transposition v4",
        "Cadenus periodic transposition v2",
        "AMSCO irregular columnar v4",
        "AMSCO double columnar v2",
        "Myszkowski transposition classic v5",
        "Myszkowski repeated letters v2",
        "Swagman route transposition v4",
        "Disrupted transposition ACA v3",
        "Incomplete columnar military v3",
        "Complete columnar military v3",
        "Double transposition SOE v5",
        "Double columnar WW2 agent v4",
        "UBCHI German army 1914 v4",
        "UBCHI pre-Nebel field v2",
        "Rail fence zigzag ancient v4",
        "Rail fence offset Redefence v4",
        "Route cipher spiral field v3",
        "Route cipher boustrophedon field v3",
        "Scytale Spartan courier v5",
        "Cardan grille Renaissance v3",
        "Cardano literary grille v3",
        "Fleissner turning grille 4x4 v4",
        "Fleissner turning grille 6x6 v4",
        "Turning grille WWI German v4",
        "ADFGX German field 1918 v4",
        "ADFGX Nebel army worksheet v2",
        "ADFGX mixed Polybius square v5",
        "ADFGVX German field 1918 v4",
        "ADFGVX Nebel army worksheet v2",
        "ADFGVX alphanumeric square v5",
        "GEDEFU field cipher v4",
        "GEDEFU checkerboard 6x6 v2",
        "Monome-Dinome checkerboard v4",
        "Monome-Dinome French trench v2",
        "Straddling checkerboard Soviet v6",
        "Straddling checkerboard classic v6",
        "Nihilist substitution overadd v5",
        "Nihilist transposition classic v4",
        "Nihilist checkerboard prison v5",
        "VIC cipher pencil-paper v7",
        "VIC checkerboard lagged key v6",
        "VIC chain addition v5",
        "VIC double transposition v4",
        "VIC disrupted transposition v4",
        "VIC sequential transposition v4",
        "Homophonic court cipher v2",
        "Homophonic Spanish 1600s v2",
        "Homophonic French 1700s v2",
        "Homophonic Zodiac table v7",
        "Zodiac 408 homophonic v6",
        "Zodiac 340 transposition v6",
        "Gold-Bug Poe cipher v5",
        "Dorabella Elgar script v5",
        "Copiale cipher glyph cluster v5",
        "Voynich EVA folio token v3",
        "Mary Queen of Scots cipher v3",
        "Babington plot nomenclator v2",
        "Elizabethan secretary cipher v2",
        "Rossignol Great Cipher syllables v6",
        "Louis XIV Great Cipher numbers v6",
        "Napoleonic codebook 1812 token",
        "Habsburg diplomatic nomenclator v2",
        "Venetian diplomatic cipher v2",
        "Papal Curia nomenclator v2",
        "Ottoman chancery code token v2",
        "Russian diplomatic code 1800s v2",
        "Zimmermann telegram code v3",
        "Zimmermann 13040 codebook v3",
        "Beale Declaration book cipher v5",
        "Book cipher page line word v3",
        "Dictionary code word number v3",
        "Bible code book cipher v3",
        "Commercial cable code ABC v2",
        "Bentley complete phrase code v2",
        "Slater telegraph code v2",
        "Western Union 92 code v2",
        "Lieber field code token v2",
        "French trench code 1916 v2",
        "German trench code 1917 v2",
        "British trench code 1918 v2",
        "SOE poem code transposition v5",
        "SOE silk map code v4",
        "Resistance handkerchief grid v4",
        "Numbers station five-figure v2",
        "Numbers station five-letter v2",
        "One-time pad letter groups v3",
        "One-time pad decimal groups v3",
        "DRYAD numeral authentication v5",
        "BATCO tactical table v5",
        "SLIDEX tactical phrase grid v5",
        "NATO brevity code v4",
        "ACP-125 operating signal v2",
        "ACP-127 message format token",
        "ACP-131 signal code v4",
        "Q-code aviation maritime v4",
        "Z-code naval signal v4",
        "Ten-code APCO v4",
        "International Code of Signals flag v3",
        "Marryat naval signal book v3",
        "Popham flag code Trafalgar v3",
        "Chappe optical telegraph v4",
        "Wigwag Myer signal v3",
        "Semaphore naval flag v3",
        "Morse international radio v4",
        "Morse American railroad v4",
        "Wabun Japanese Morse v3",
        "Baudot ITA1 code v3",
        "Baudot ITA2 teleprinter v4",
        "Murray teleprinter code v4",
        "Vernam 1917 Baudot XOR v4",
        "Vernam one-time tape v4",
        "Rockex II tape cipher v5",
        "SIGTOT one-time tape v4",
        "SIGSALY voice secrecy token",
        "HY-2 voice scrambler style v2",
        "STU secure voice token v2",
        "Hebern single rotor v4",
        "Hebern five-rotor machine v4",
        "Kryha Standard cipher machine v4",
        "Kryha Liliput disk v2",
        "Enigma commercial D v4",
        "Enigma K Swiss army v4",
        "Enigma I Wehrmacht v4",
        "Enigma M3 Navy v4",
        "Enigma M4 U-boat v4",
        "Enigma G Abwehr v4",
        "Enigma Railway Rocket v3",
        "Enigma Tirpitz Japan v4",
        "Enigma Uhr plugboard v3",
        "Typex Mark II five-rotor v3",
        "Typex Mark VI rotor v3",
        "Typex Mark VIII rotor v3",
        "SIGABA CSP-889 v4",
        "SIGABA CSP-2900 v4",
        "SIGABA index rotor v3",
        "NEMA Swiss army v5",
        "Fialka M-125 Cyrillic v5",
        "Fialka Latin training v5",
        "KL-7 ADONIS rotor v5",
        "Hagelin C-35 pinwheel v2",
        "Hagelin C-36 pinwheel v3",
        "Hagelin C-38 converter v3",
        "Hagelin C-52 lug cage v5",
        "Hagelin CX-52 v5",
        "Hagelin CD-57 pocket v5",
        "Hagelin M-209 converter v5",
        "M-209-B field converter v2",
        "Lorenz SZ40 chi wheels v5",
        "Lorenz SZ42 psi wheels v6",
        "Lorenz SZ42 motor wheels v3",
        "Siemens T52a Sturgeon v3",
        "Siemens T52d Sturgeon v4",
        "Siemens T52e Sturgeon v3",
        "Siemens T43 tape machine v3",
        "Purple diplomatic machine v6",
        "Japanese Red machine v4",
        "Japanese Orange attaché v3",
        "Japanese Coral machine v2",
        "Japanese Jade machine v2",
        "JN-25 naval codebook v2",
        "JN-40 merchant code token",
        "British Naval Cypher No 3 v2",
        "British Government Code Cypher v2",
        "US Army SIGTOT v4",
        "KW-26 ROMULUS line cipher v5",
        "KW-7 ORESTES line cipher v5",
        "KW-37 fleet broadcast cipher token",
        "KL-51 field cipher token",
        "Rockex one-time tape v5",
        "Soviet OTP five-figure v3",
        "Soviet OTP five-letter v4",
        "Soviet Fialka training key v5"
    ]
}

IsV40RealWorldMode(name) {
    for _, item in V40ModeNames() {
        if name = item
            return true
    }
    return false
}

V40RealWorldLetter(letter) {
    global modeName

    ; v40 labels are real-world / historical systems adapted to safe live typing.
    ; Wheel, rotor, tape, codebook and tactical systems are routed through stable
    ; local transformations so startup self-check remains deterministic.
    if V37ContainsAny(modeName, ["ADFGX", "ADFGVX", "GEDEFU", "Polybius", "Checkerboard", "Monome", "Straddling", "Nihilist", "VIC", "DRYAD", "BATCO", "SLIDEX", "Q-code", "Z-code", "ACP-", "Brevity", "Ten-code", "Gematria"])
        return V37PolybiusStyleToken(letter)

    if V37ContainsAny(modeName, ["Morse", "Baudot", "Murray", "Vernam", "Wigwag", "Chappe", "Popham", "Marryat", "Semaphore", "Signal", "flag", "telegraph", "teleprinter", "sounder", "Wabun", "ITA1", "ITA2", "SIGSALY", "voice"])
        return V37SignalStyleToken(letter)

    if V37ContainsAny(modeName, ["Enigma", "Typex", "SIGABA", "NEMA", "Fialka", "KL-7", "Hagelin", "Hebern", "Kryha", "Lorenz", "Siemens", "Purple", "Japanese", "Rockex", "KW-", "SIGTOT", "HY-", "STU", "M-209", "M-94", "M-138", "Jefferson", "Bazeries", "Aeneas", "Alberti", "Saint-Cyr", "Wheatstone", "Della Porta", "disk", "Disk", "wheel", "Wheel", "rotor", "Rotor"])
        return V37MachineStyleLetter(letter)

    if V37ContainsAny(modeName, ["Dorabella", "Gold-Bug", "Copiale", "Voynich", "Ogham", "Runic", "Futhark", "Templar", "Masonic", "Freemason", "Rosicrucian", "Theban", "Malachim", "Celestial", "Enochian", "Cistercian", "Tironian", "symbol", "glyph", "notch", "rune", "Kabbalistic", "Temurah", "notarikon"])
        return V37SymbolStyleToken(letter)

    if V37ContainsAny(modeName, ["Nomenclator", "Rossignol", "Louis XIV", "Great Cipher", "Beale", "Zimmermann", "Code", "code", "codebook", "Cypher", "phrase", "Dictionary", "Book", "Bible", "Mary", "Elizabeth", "Babington", "NATO", "Western Union", "Bentley", "ABC", "Slater", "Lieber", "Napoleonic", "Venetian", "Papal", "Ottoman", "Russian", "JN-", "Naval", "Government"])
        return V37CodebookStyleToken(letter)

    if V37ContainsAny(modeName, ["Route", "Rail", "Redefence", "AMSCO", "Cadenus", "Swagman", "Myszkowski", "Columnar", "UBCHI", "grille", "Grille", "Fleissner", "Scytale", "Cardan", "Cardano", "transposition", "Transposition", "boustrophedon"])
        return V37TranspositionStyleToken(letter)

    if V37ContainsAny(modeName, ["Playfair", "Doppelkasten", "Two-square", "Four-square", "Bifid", "Trifid", "Delastelle", "Digrafid", "Portax", "Phillips"])
        return V37PolybiusStyleToken(letter)

    return V37PolyalphabeticStyleLetter(letter)
}
