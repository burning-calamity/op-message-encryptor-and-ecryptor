# APK v1 Build Notes

This folder is now an Android-oriented Kivy project wrapper around the cipher
engine in `encripter.py`.

## Files

- `main.py` — Kivy entrypoint used by Buildozer. It imports `encripter.py` and
  exposes the registry through a simple mobile UI.
- `encripter.py` — copied cipher engine/source module.
- `buildozer.spec` — Buildozer configuration for producing an Android APK.
- `requirements.txt` — Python dependency hint for local tooling.

## Build from Linux

```bash
cd apk/v1
python3 -m pip install --user buildozer
buildozer android debug
```

The debug APK should be produced under `apk/v1/bin/` if the Android SDK/NDK and
Buildozer prerequisites are installed correctly.

## Notes

The original desktop Tkinter GUI in `encripter.py` is not used by the APK. The
APK starts from `main.py`, which uses Kivy widgets instead.
