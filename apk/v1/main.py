"""Kivy APK entrypoint for the All-The-Ciphers toolkit.

This module intentionally avoids the desktop Tkinter GUI in encripter.py and
wraps the shared cipher registry with a small Android-friendly Kivy interface.
Buildozer treats a file named main.py as the application entrypoint.
"""

from __future__ import annotations

from typing import Dict

from kivy.app import App
from kivy.core.clipboard import Clipboard
from kivy.metrics import dp
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.label import Label
from kivy.uix.scrollview import ScrollView
from kivy.uix.spinner import Spinner
from kivy.uix.textinput import TextInput

import encripter


class CipherMobileRoot(BoxLayout):
    """Minimal Kivy UI that exposes the encripter registry on Android."""

    def __init__(self, **kwargs):
        super().__init__(orientation="vertical", padding=dp(8), spacing=dp(8), **kwargs)
        self.registry = encripter.get_registry()
        self.registry_by_name = {entry.name: entry for entry in self.registry}
        self.param_inputs: Dict[str, TextInput] = {}

        self.add_widget(self._build_toolbar())
        self.add_widget(self._build_params_panel())
        self.add_widget(self._build_text_panels())
        self.add_widget(self._build_actions())

        self._refresh_params()

    def _build_toolbar(self) -> BoxLayout:
        toolbar = BoxLayout(orientation="horizontal", size_hint_y=None, height=dp(48), spacing=dp(8))
        self.cipher_spinner = Spinner(
            text=self.registry[0].name,
            values=[entry.name for entry in self.registry],
            size_hint_x=0.7,
        )
        self.cipher_spinner.bind(text=lambda *_: self._refresh_params())
        self.mode_spinner = Spinner(text="encode", values=("encode", "decode"), size_hint_x=0.3)
        toolbar.add_widget(self.cipher_spinner)
        toolbar.add_widget(self.mode_spinner)
        return toolbar

    def _build_params_panel(self) -> ScrollView:
        scroll = ScrollView(size_hint_y=None, height=dp(96), do_scroll_x=False)
        self.params_box = BoxLayout(orientation="vertical", spacing=dp(4), size_hint_y=None)
        self.params_box.bind(minimum_height=self.params_box.setter("height"))
        scroll.add_widget(self.params_box)
        return scroll

    def _build_text_panels(self) -> BoxLayout:
        panels = BoxLayout(orientation="vertical", spacing=dp(8))
        panels.add_widget(Label(text="Input", size_hint_y=None, height=dp(24), halign="left"))
        self.input_text = TextInput(multiline=True, text="", size_hint_y=0.45)
        panels.add_widget(self.input_text)
        panels.add_widget(Label(text="Output", size_hint_y=None, height=dp(24), halign="left"))
        self.output_text = TextInput(multiline=True, readonly=True, text="", size_hint_y=0.45)
        panels.add_widget(self.output_text)
        return panels

    def _build_actions(self) -> BoxLayout:
        actions = BoxLayout(orientation="horizontal", size_hint_y=None, height=dp(48), spacing=dp(8))
        run_btn = Button(text="Run")
        run_btn.bind(on_release=lambda *_: self._run_cipher())
        swap_btn = Button(text="Swap")
        swap_btn.bind(on_release=lambda *_: self._swap_text())
        copy_btn = Button(text="Copy")
        copy_btn.bind(on_release=lambda *_: Clipboard.copy(self.output_text.text))
        clear_btn = Button(text="Clear")
        clear_btn.bind(on_release=lambda *_: self._clear_text())
        for button in (run_btn, swap_btn, copy_btn, clear_btn):
            actions.add_widget(button)
        return actions

    def _refresh_params(self) -> None:
        self.params_box.clear_widgets()
        self.param_inputs.clear()
        entry = self.registry_by_name[self.cipher_spinner.text]
        if not entry.params:
            self.params_box.add_widget(Label(text="No parameters", size_hint_y=None, height=dp(32)))
            return
        for param in entry.params:
            row = BoxLayout(orientation="horizontal", size_hint_y=None, height=dp(40), spacing=dp(6))
            row.add_widget(Label(text=param.label, size_hint_x=0.35))
            value = TextInput(text=param.default, multiline=False, size_hint_x=0.65)
            self.param_inputs[param.name] = value
            row.add_widget(value)
            self.params_box.add_widget(row)

    def _params(self) -> Dict[str, str]:
        return {name: widget.text for name, widget in self.param_inputs.items()}

    def _run_cipher(self) -> None:
        try:
            if self.mode_spinner.text == "decode":
                result = encripter.call_decode(self.cipher_spinner.text, self.input_text.text, self._params())
            else:
                result = encripter.call_encode(self.cipher_spinner.text, self.input_text.text, self._params())
        except Exception as exc:  # Surface errors in the mobile UI instead of crashing the Activity.
            result = f"Err:{exc}"
        self.output_text.text = result

    def _swap_text(self) -> None:
        self.input_text.text, self.output_text.text = self.output_text.text, self.input_text.text

    def _clear_text(self) -> None:
        self.input_text.text = ""
        self.output_text.text = ""


class AllTheCiphersApp(App):
    title = "All-The-Ciphers"

    def build(self):
        return CipherMobileRoot()


if __name__ == "__main__":
    AllTheCiphersApp().run()
