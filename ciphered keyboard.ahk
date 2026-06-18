#Requires AutoHotkey v2.0
#SingleInstance Force
#UseHook True

; Live Cipher GUI — filtered settings + Enigma M3/M4 + expanded live ciphers
; Ctrl+Alt+E = Toggle encryption
; Ctrl+Alt+R = Reset cipher state
; Ctrl+Alt+Q = Quit

; ------------------------------------------------------------
; Globals
; ------------------------------------------------------------

global ALPHABET := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

global MODE_LIST := [
    "Enigma M3",
    "Enigma M4",
    "Caesar",
    "Progressive Caesar",
    "Trithemius",
    "ROT13",
    "Atbash",
    "Vigenere",
    "Autokey Vigenere",
    "Gronsfeld",
    "Running Key Vigenere",
    "Beaufort",
    "Variant Beaufort",
    "Porta",
    "Affine",
    "Keyword substitution",
    "Random substitution",
    "QWERTY to Dvorak",
    "QWERTY to AZERTY",
    "Keyboard mirror",
    "Leet basic",
    "Morse letters",
    "Binary 5-bit",
    "Baconian A/B",
    "A1Z26 numbers",
    "Polybius square",
    "Tap code",
    "ADFGX",
    "ADFGVX",
    "Straddling checkerboard",
    "Monome-Dinome",
    "Pollux Morse",
    "Base64 per letter",
    "URL percent",
    "HTML entity",
    "Unicode code point",
    "ASCII binary 8-bit",
    "XOR hex with key",
    "XOR binary with key",
    "Braille",
    "Pigpen symbols",
    "Emoji alphabet",
    "Letter index hex",
    "Roman numerals",
    "Prime numbers",
    "Squared A1Z26",
    "Condi",
    "Chaocipher",
    "Playfair pairs",
    "Hill 2x2 pairs",
    "Bifid pairs",
    "Two-square pairs",
    "Four-square pairs",
    "Nihilist substitution",
    "Trifid coordinates",
    "Checkerboard coordinates",
    "Baudot ITA2",
    "Gray code 5-bit",
    "BCD A1Z26",
    "Fibonacci numbers",
    "Triangular numbers",
    "Cubed A1Z26",
    "Factorial index",
    "Modulo 9 index",
    "Reverse alphabet index",
    "Keyboard Caesar",
    "Vowel Caesar",
    "Consonant Caesar",
    "Alternating Caesar",
    "Elder Futhark runes",
    "Ogham letters",
    "Semaphore text",
    "Masonic pigpen variant",
    "Hex ASCII",
    "ASCII decimal",
    "Octal ASCII",
    "Fullwidth letters",
    "Upside-down letters",
    "Greek lookalike",
    "Cyrillic lookalike",
    "NATO words"
]

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

; GUI references
global mainGui := ""
global headerText1 := "", headerText2 := "", enableBox := "", autoResetBox := ""
global modeBox := "", presetBox := "", applyPresetBtn := ""
global settingTitleText := "", settingHintText := ""
global outputModeBox := "", applyBtn := "", resetBtn := "", testBtn := "", quitBtn := ""
global previewInputLabel := "", previewInput := "", previewOutputLabel := "", previewOutput := ""
global statusText := "", stateText := "", hotkeyText := "", noteText := ""

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

BuildGui()
return

; ------------------------------------------------------------
; Hotkeys
; ------------------------------------------------------------

^!e::ToggleEnabledFromHotkey()
^!r::ResetStateFromHotkey()
^!q::ExitApp

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
#HotIf

; ------------------------------------------------------------
; GUI construction
; ------------------------------------------------------------

BuildGui() {
    global mainGui, headerText1, headerText2, enableBox, autoResetBox, modeBox, presetBox, applyPresetBtn
    global settingTitleText, settingHintText, outputModeBox, applyBtn, resetBtn, testBtn, quitBtn
    global previewInputLabel, previewInput, previewOutputLabel, previewOutput, statusText, stateText, hotkeyText, noteText
    global MODE_LIST, modeName, autoResetOnEnable, enabled

    mainGui := Gui("+AlwaysOnTop +Resize +MinSize900x700", "Live Typing Cipher — Random Presets + More Ciphers")
    mainGui.SetFont("s10", "Segoe UI")
    mainGui.MarginX := 16
    mainGui.MarginY := 12

    headerText1 := mainGui.AddText("xm y12 w980", "System-wide live typing cipher")
    headerText2 := mainGui.AddText("xm y36 w980", "Only settings for the selected cipher are visible. The GUI is ignored while live typing is enabled, so settings remain editable.")

    enableBox := mainGui.AddCheckBox("xm y76 w160", "Enable now")
    enableBox.Value := enabled ? 1 : 0
    enableBox.OnEvent("Click", EnableClicked)

    autoResetBox := mainGui.AddCheckBox("x190 y76 w240", "Reset state when enabling")
    autoResetBox.Value := autoResetOnEnable ? 1 : 0

    mainGui.AddText("xm y116 w90", "Mode:")
    modeBox := mainGui.AddDropDownList("x82 y112 w240", MODE_LIST)
    modeBox.Choose(IndexOf(MODE_LIST, modeName))
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
    noteText := mainGui.AddText("xm y772 w980", "Notes: Random presets generate new settings every time. Some modes output multiple characters per letter. Pair modes such as Playfair, Hill, Bifid, Two-square, and Four-square wait for two letters before output.")

    mainGui.OnEvent("Close", (*) => ExitApp())
    mainGui.OnEvent("Size", GuiResized)

    RefreshPresetList("Custom")
    UpdateModePanel()
    UpdateStatus()
    mainGui.Show("w1040 h830")
}

BuildSettingsPanels(gui) {
    global allSettingControls, enigmaPanelControls, enigmaM4OnlyControls, caesarPanelControls, keyPanelControls, affinePanelControls, substitutionPanelControls
    global thinLabel, thinBox, leftLabel, leftBox, middleLabel, middleBox, rightLabel, rightBox
    global reflectorLabel, reflectorBox, startLabel, startEdit, ringsLabel, ringsEdit, plugboardLabel, plugboardEdit
    global shiftLabel, shiftEdit, keyLabel, keyEdit, affineALabel, affineAEdit, affineBLabel, affineBEdit
    global substitutionLabel, substitutionEdit, randBtn
    global ROTOR_NAMES, THIN_ROTOR_NAMES, REFLECTOR_M3_NAMES

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
    for _, list in [enigmaPanelControls, caesarPanelControls, keyPanelControls, affinePanelControls, substitutionPanelControls] {
        for _, ctrl in list
            allSettingControls.Push(ctrl)
    }
}

GuiResized(thisGui, minMax, width, height) {
    global headerText1, headerText2, settingTitleText, settingHintText, presetBox, applyPresetBtn
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
    m["Hex ASCII"] := ["Custom", "Hex ASCII"]
    m["ASCII decimal"] := ["Custom", "ASCII decimal"]
    m["Octal ASCII"] := ["Custom", "Octal ASCII"]
    m["Fullwidth letters"] := ["Custom", "Fullwidth letters"]
    m["Upside-down letters"] := ["Custom", "Upside-down letters"]
    m["Greek lookalike"] := ["Custom", "Greek lookalike"]
    m["Cyrillic lookalike"] := ["Custom", "Cyrillic lookalike"]
    m["NATO words"] := ["Custom", "NATO words"]
    return m
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

ModeChanged(*) {
    global modeBox, MODE_LIST, modeName
    modeName := SelectedFrom(modeBox, MODE_LIST)
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
    if preset = "Custom"
        return

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

        case "Random substitution — random 1", "Random substitution — random 2", "Random substitution — random 3", "Random substitution — random now":
            substitutionEdit.Value := RandomAlphabet()
        case "Random substitution — QWERTY fixed":
            substitutionEdit.Value := "QWERTYUIOPASDFGHJKLZXCVBNM"
        case "Random substitution — reverse fixed":
            substitutionEdit.Value := "ZYXWVUTSRQPONMLKJIHGFEDCBA"
    }

    return FinishPresetApply(preset)
}

FinishPresetApply(preset) {
    ApplySettingsCore(false)
    ResetState()
    UpdateStatus()
    ToolTip "Preset applied: " . preset
    SetTimer () => ToolTip(), -1200
}

SetEnigmaPreset(model, thin, left, middle, right, reflector, start, rings, plugPairs) {
    global modeName, modeBox, MODE_LIST, thinBox, leftBox, middleBox, rightBox, reflectorBox, startEdit, ringsEdit, plugboardEdit
    global THIN_ROTOR_NAMES, ROTOR_NAMES

    modeName := model
    modeBox.Choose(IndexOf(MODE_LIST, model))
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
    global modeName, allSettingControls, enigmaPanelControls, enigmaM4OnlyControls, caesarPanelControls, keyPanelControls, affinePanelControls, substitutionPanelControls
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
    } else if modeName = "Caesar" || modeName = "Progressive Caesar" || modeName = "Trithemius" || modeName = "Keyboard Caesar" || modeName = "Vowel Caesar" || modeName = "Consonant Caesar" || modeName = "Alternating Caesar" {
        SetControlsVisible(caesarPanelControls, true)
        settingHintText.Value := "Shift settings: Caesar uses a fixed shift; Progressive Caesar and Trithemius use this as the starting shift."
    } else if modeName = "Vigenere" || modeName = "Autokey Vigenere" || modeName = "Gronsfeld" || modeName = "Running Key Vigenere" || modeName = "Beaufort" || modeName = "Variant Beaufort" || modeName = "Porta" || modeName = "Keyword substitution" || modeName = "XOR hex with key" || modeName = "XOR binary with key" || modeName = "Condi" || modeName = "Playfair pairs" || modeName = "Bifid pairs" || modeName = "Two-square pairs" || modeName = "Four-square pairs" || modeName = "Nihilist substitution" {
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
    global modeBox, MODE_LIST, modeName, enabled, enableBox, autoResetBox, autoResetOnEnable
    global thinBox, leftBox, middleBox, rightBox, reflectorBox, startEdit, ringsEdit, plugboardEdit
    global THIN_ROTOR_NAMES, ROTOR_NAMES, enigmaThin, enigmaLeft, enigmaMiddle, enigmaRight, enigmaReflector, enigmaStart, enigmaRings, plugboardPairs, plugboard
    global shiftEdit, keyEdit, affineAEdit, affineBEdit, substitutionEdit, outputModeBox
    global shiftValue, keyText, affineA, affineB, substitutionAlphabet, outputMode

    modeName := SelectedFrom(modeBox, MODE_LIST)
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
    if modeName = "Gronsfeld" {
        if CleanDigits(keyText) = "" {
            keyText := "31415"
            keyEdit.Value := keyText
        }
    } else if modeName = "Vigenere" || modeName = "Autokey Vigenere" || modeName = "Running Key Vigenere" || modeName = "Beaufort" || modeName = "Variant Beaufort" || modeName = "Porta" || modeName = "Keyword substitution" || modeName = "Condi" || modeName = "Playfair pairs" || modeName = "Bifid pairs" || modeName = "Two-square pairs" || modeName = "Four-square pairs" || modeName = "Nihilist substitution" {
        if CleanLetters(keyText) = "" {
            keyText := "KEY"
            keyEdit.Value := keyText
        }
    } else if modeName = "XOR hex with key" || modeName = "XOR binary with key" {
        if keyText = "" {
            keyText := "KEY"
            keyEdit.Value := keyText
        }
    }

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
    global rotorPositions, enigmaStart, streamIndex, autoKeyHistory, pairBuffer, condiShift, chaosLeft, chaosRight, chaosLeftDefault, chaosRightDefault
    rotorPositions := StrSplit(enigmaStart)
    streamIndex := 0
    autoKeyHistory := ""
    pairBuffer := ""
    condiShift := 0
    chaosLeft := chaosLeftDefault
    chaosRight := chaosRightDefault
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
        case "NATO words":
            return NatoLetter(letter)
    }
    return letter
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
    qwerty := "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    azerty := "QBCDEFGHIJRL,NPASSTVZXYW" ; fallback corrected below by map
    m := Map("A","Q","Q","A","W","Z","Z","W","M",",","B","B","C","C","D","D","E","E","F","F","G","G","H","H","I","I","J","J","K","K","L","L","N","N","O","O","P","P","R","R","S","S","T","T","U","U","V","V","X","X","Y","Y")
    u := StrUpper(letter)
    out := m.Has(u) ? m[u] : u
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
    a := pairBuffer
    pairBuffer := ""
    switch modeName {
        case "Playfair pairs":
            return PlayfairEncryptPair(a, "X", true)
        case "Hill 2x2 pairs":
            return Hill2x2EncryptPair(a, "X", true)
        case "Bifid pairs":
            return BifidEncryptPair(a, "X", true)
        case "Two-square pairs":
            return TwoSquareEncryptPair(a, "X", true)
        case "Four-square pairs":
            return FourSquareEncryptPair(a, "X", true)
    }
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
