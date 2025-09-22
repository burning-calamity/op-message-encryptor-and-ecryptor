 ì*-+
 # math_lab_gui.py
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from sympy import (
    symbols, Symbol, Eq, sympify, Lambda, S,
    solve, nsolve, expand, factor, simplify, apart,
    diff, integrate, limit as sym_limit, series, oo, Matrix, Poly, roots,
    dsolve, Function, Derivative, lambdify,
    factorint, gcd, lcm, sqrt, pi, E, I
)
# Residue (optional across SymPy versions)
try:
    from sympy import residue as sym_residue
except Exception:
    sym_residue = None

from sympy.core.sympify import SympifyError
from sympy.parsing.sympy_parser import (
    parse_expr, standard_transformations,
    implicit_multiplication_application, convert_xor
)
from sympy.logic.boolalg import simplify_logic
import mpmath as mp
import re
import numpy as np

# Optional plotting (matplotlib)
try:
    import matplotlib
    matplotlib.use("TkAgg")
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
    from matplotlib.figure import Figure
    HAVE_MPL = True
except Exception:
    HAVE_MPL = False

TRANSFORMS = standard_transformations + (
    implicit_multiplication_application,
    convert_xor,  # allow ^
)

MODES = [
    "Automatic",
    "Solve (equation or system)",
    "Expand",
    "Factor",
    "Simplify",
    "Partial Fractions (apart)",
    "Polynomial Tools",
    "Differentiate",
    "Integrate",
    "Limit",
    "Series (Taylor)",
    "Gradient",
    "Jacobian",
    "Hessian",
    "Divergence",
    "Curl",
    "Define function(s)",
    "Call function / Evaluate",
    "Plot 1D",
    "Plot 2D Contour",
    "Plot 2D Surface (3D)*",
    "Plot Implicit F(x,y)=0",
    "Plot Parametric 2D",
    "Plot Polar",
    "Plot Quiver (vector field)",
    "ODE: dsolve (symbolic)",
    "ODE: numeric (mpmath)",
    "Optimization: critical points",
    "Optimization: Lagrange (1 constraint)",
    "Linear Algebra",
    "Complex Residue",
    "Logic: truth table & simplify",
    "Number Theory",
]

HELP_TEXT = r"""
NEW: Automatic mode guesses what you want:
  • "y = 2x + 3"            → plots the line, slope & intercepts
  • "y=sin(x); y=cos(x)"    → plots multiple lines (legend)
  • "x + y = 3; x - y = 1"  → solves the system
  • "x^2 + y^2 = 1"         → plots the implicit curve (circle)
  • "f(x) = (1+3x)^(-x/2)"  → defines function f
  • "sin(x)/x"              → plots over default x-range
  • "(x+1)^5"               → expands & shows result

PARAMS (mini-language):
  Differentiate:       x:2, y:1
  Integrate:           x:0:1; y
  Limit:               x->0+   or   x->oo
  Series:              x=0; order=6
  Solve nsolve:        guess: [1, 1]
  Plot 1D:             x: -5:5; points=400; legend=My f(x)
  Plot Implicit:       x: -3:3; y: -3:3; points=400
  Plot Contour:        x: -3:3; y: -3:3; levels=20; points=200
  Plot 3D Surface:     x: -3:3; y: -3:3; points=80
  Parametric 2D:       t: 0:6.283; points=500    (INPUT: [x(t), y(t)])
  Polar:               th: 0:6.283; points=500   (INPUT: r(th))
  Quiver:              x: -3:3; y: -3:3; points=20  (INPUT: [P(x,y), Q(x,y)])
  ODE numeric:         tspan: 0:10; y0: [1, 0]; steps=1000
  Lagrange:            constraint: g(x,y)=0

TIPS:
  - Implicit multiplication OK (2x, 3xy, x(x+1))
  - Use parentheses for non-integer exponents: (1+3x)^(-x/2)
  - Separate multiple 'y = ...' with ';' to draw several lines
"""

# ---------- Regex / helpers ----------
FUNC_DEF_RE     = re.compile(r"^\s*([A-Za-z_]\w*)\s*\(\s*([A-Za-z0-9_,\s]*)\s*\)\s*=\s*(.+)$")
LINE_Y_EQ_RE    = re.compile(r"^\s*y\s*=\s*(.+)$", re.IGNORECASE)   # e.g., "y = 2x+3"
IMPLICIT_EQ_RE  = re.compile(r"^[^=]+=[^=]+$")                      # single equation with '='

def parse_expr_safe(s, local_dict):
    return parse_expr(s, transformations=TRANSFORMS, local_dict=local_dict)

def parse_vars(var_text):
    names = [v.strip() for v in var_text.split(",") if v.strip()]
    return symbols(",".join(names)) if names else tuple()

def parse_equations(text, ldict):
    eqs = []
    for raw in text.replace("\n", ";").split(";"):
        t = raw.strip()
        if not t:
            continue
        if "=" in t:
            L, R = t.split("=", 1)
            eqs.append(Eq(parse_expr_safe(L, ldict), parse_expr_safe(R, ldict)))
        else:
            eqs.append(Eq(parse_expr_safe(t, ldict), sympify(0)))
    if not eqs:
        raise ValueError("No equations found.")
    return eqs

def parse_diff_params(ptext, default_vars):
    if not ptext.strip():
        if not default_vars:
            raise ValueError("Set VARIABLES or specify vars in Params.")
        return [(str(v), 1) for v in default_vars]
    parts = [p.strip() for p in ptext.split(",") if p.strip()]
    out = []
    for p in parts:
        if ":" in p:
            v, n = p.split(":", 1)
            out.append((v.strip(), int(n.strip())))
        else:
            out.append((p.strip(), 1))
    return out

def parse_integral_params(ptext, ldict):
    if not ptext.strip():
        return []
    items = [seg.strip() for seg in ptext.replace("\n", ";").split(";") if seg.strip()]
    out = []
    for it in items:
        if ":" in it:
            parts = it.split(":")
            if len(parts) != 3:
                raise ValueError(f"Bad integral spec: {it} (use var:a:b)")
            v, a, b = parts
            out.append((v.strip(), (parse_expr_safe(a.strip(), ldict), parse_expr_safe(b.strip(), ldict))))
        else:
            out.append((it.strip(), None))
    return out

def parse_limit_params(ptext, ldict):
    if "->" not in ptext:
        raise ValueError("Limit params must look like 'x->0' or 'x->0+'")
    var, to = [x.strip() for x in ptext.split("->", 1)]
    direction = "+"
    if to.endswith(("+", "-")):
        direction = to[-1]
        to = to[:-1].strip()
    point = {"oo": oo, "+oo": oo, "-oo": -oo}.get(to, parse_expr_safe(to, ldict))
    return var, point, direction

def parse_series_params(ptext, ldict):
    stuff = [s.strip() for s in ptext.replace("\n", ";").split(";") if s.strip()]
    var = None
    point = None
    order = 6
    for s in stuff:
        if "=" in s and "order" not in s.lower():
            v, p = [x.strip() for x in s.split("=", 1)]
            var = v
            point = parse_expr_safe(p, ldict)
        elif s.lower().startswith("order"):
            _, n = [x.strip() for x in s.split("=", 1)]
            order = int(n)
    if var is None or point is None:
        raise ValueError("Series needs 'var=point; order=N'.")
    if order < 1:
        raise ValueError("Order must be >= 1.")
    return var, point, order

def parse_range_params(ptext, ldict, axis='x', default=(-5,5), default_points=400):
    a, b = default
    pts = default_points
    legend = None
    for seg in [s.strip() for s in ptext.replace("\n",";").split(";") if s.strip()]:
        low = seg.lower()
        if low.startswith(f"{axis}:"):
            _, r = seg.split(":", 1)
            r = r.strip()
            lo, hi = [t.strip() for t in r.split(":")]
            a = parse_expr_safe(lo, ldict)
            b = parse_expr_safe(hi, ldict)
        elif low.startswith("points"):
            _, v = seg.split("=", 1)
            pts = int(v.strip())
        elif low.startswith("legend"):
            _, v = seg.split("=", 1)
            legend = v.strip()
    return (float(a), float(b), int(pts), legend)

def parse_2d_params(ptext, ldict, default=(-3,3), default_points=200, default_levels=20):
    xa, xb, xn, _ = parse_range_params(ptext, ldict, 'x', default, default_points)
    ya, yb, yn, _ = parse_range_params(ptext, ldict, 'y', default, default_points)
    levels = default_levels
    for seg in [s.strip() for s in ptext.replace("\n",";").split(";") if s.strip()]:
        low = seg.lower()
        if low.startswith("levels"):
            _, v = seg.split("=", 1)
            levels = int(v.strip())
    return xa, xb, xn, ya, yb, yn, levels

def parse_guess_from_params(ptext, ldict):
    marker = "guess:"
    i = ptext.find(marker)
    if i == -1:
        return None
    arr = ptext[i+len(marker):].strip()
    if not (arr.startswith("[") or arr.startswith("(")):
        raise ValueError("nsolve guess must be a list or tuple, e.g., guess: [1, 1]")
    vec = parse_expr_safe(arr, ldict)
    if hasattr(vec, "__iter__"):
        return [sympify(v) for v in list(vec)]
    raise ValueError("Guess must be a list/tuple.")

def try_sympy_residue(expr, zsym, point):
    if sym_residue is not None:
        return sym_residue(expr, zsym, point)
    # simple-pole fallback
    return sym_limit((zsym - point) * expr, zsym, point)

# ---------- Main App ----------
class MathLab(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Skibidi calculator 3000")
        self.geometry("1120x840")
        self.minsize(1000, 760)

        # Environment
        self.funcs = {}   # name -> (args [Symbol], Lambda)
        self.locals = {}  # parse env

        # Top controls
        top = ttk.Frame(self, padding=12)
        top.pack(fill="x")
        ttk.Label(top, text="Mode:").grid(row=0, column=0, sticky="w")
        self.mode = tk.StringVar(value=MODES[0])
        ttk.Combobox(top, textvariable=self.mode, values=MODES, state="readonly", width=36)\
            .grid(row=0, column=1, sticky="w", padx=(6, 12))
        self.numeric = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Numeric approximation", variable=self.numeric)\
            .grid(row=0, column=2, sticky="w")
        self.use_nsolve = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Try nsolve (needs guess)", variable=self.use_nsolve)\
            .grid(row=0, column=3, sticky="w")
        self.show_grid = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="Grid", variable=self.show_grid)\
            .grid(row=0, column=4, sticky="w")
        ttk.Button(top, text="Help", command=self.show_help).grid(row=0, column=5, sticky="e")
        ttk.Button(top, text="Copy last line", command=self.copy_last_line).grid(row=0, column=6, sticky="e")

        # Input frame
        in_frame = ttk.LabelFrame(self, text="Input", padding=12)
        in_frame.pack(fill="both", expand=False, padx=12, pady=(6, 0))
        ttk.Label(in_frame, text="Expression / Equation(s) / Function(s):").grid(row=0, column=0, sticky="w")
        self.expr_box = tk.Text(in_frame, height=8, wrap="word")
        self.expr_box.grid(row=1, column=0, columnspan=4, sticky="nsew", pady=(4, 8))
        self.expr_box.insert("1.0", "y = 2x + 3")

        ttk.Label(in_frame, text="Variables (comma-separated):").grid(row=2, column=0, sticky="w")
        self.vars_entry = ttk.Entry(in_frame, width=40)
        self.vars_entry.grid(row=2, column=1, sticky="we", padx=(6, 12))
        self.vars_entry.insert(0, "x, y, z, t")

        ttk.Label(in_frame, text="Params (mode-specific):").grid(row=2, column=2, sticky="w")
        self.params_entry = ttk.Entry(in_frame)
        self.params_entry.grid(row=2, column=3, sticky="we", padx=(6, 0))
        self.params_entry.insert(0, "")

        in_frame.columnconfigure(1, weight=1)
        in_frame.columnconfigure(3, weight=1)

        # Buttons
        btns = ttk.Frame(self, padding=(12, 8))
        btns.pack(fill="x")
        ttk.Button(btns, text="Run", command=self.run).pack(side="left")
        ttk.Button(btns, text="Clear Output", command=self.clear_output).pack(side="left", padx=(8, 0))
        ttk.Button(btns, text="List Functions", command=self.list_functions).pack(side="left", padx=(8, 0))
        ttk.Button(btns, text="Save Plot", command=self.save_plot).pack(side="left", padx=(8, 0))

        # Plot area + toolbar
        plot_frame = ttk.LabelFrame(self, text="Plot (if used)", padding=6)
        plot_frame.pack(fill="both", expand=False, padx=12, pady=(0, 8))
        if HAVE_MPL:
            self.figure = Figure(figsize=(7.2, 3.9), dpi=100)
            self.canvas = FigureCanvasTkAgg(self.figure, master=plot_frame)
            self.ax = self.figure.add_subplot(111)
            self.canvas.get_tk_widget().pack(fill="both", expand=True)
            toolbar = NavigationToolbar2Tk(self.canvas, plot_frame)
            toolbar.update()
        else:
            self.figure = None
            self.canvas = None
            ttk.Label(plot_frame, text="Matplotlib not available — plotting modes will show text only.").pack(fill="x")

        # Output
        out_frame = ttk.LabelFrame(self, text="Output", padding=12)
        out_frame.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        self.output = tk.Text(out_frame, wrap="word")
        self.output.pack(fill="both", expand=True)

        # Status
        self.status = tk.StringVar(value="Ready.")
        ttk.Label(self, textvariable=self.status, anchor="w", padding=(12, 6)).pack(fill="x")

        try:
            ttk.Style().theme_use("clam")
        except Exception:
            pass

    # ---------- Utilities ----------
    def write(self, *lines):
        for L in lines:
            s = str(L)
            if not s.endswith("\n"):
                s += "\n"
            self.output.insert("end", s)

    def clear_output(self):
        self.output.delete("1.0", tk.END)
        self.status.set("Cleared.")

    def show_help(self):
        messagebox.showinfo("Help", HELP_TEXT)

    def copy_last_line(self):
        txt = self.output.get("1.0", "end").strip().splitlines()
        if not txt:
            return
        last = txt[-1]
        self.clipboard_clear()
        self.clipboard_append(last)
        self.status.set("Copied last line to clipboard.")

    def save_plot(self):
        if not self.canvas:
            messagebox.showwarning("No plot", "No plot to save.")
            return
        fname = filedialog.asksaveasfilename(defaultextension=".png",
                                             filetypes=[("PNG", "*.png"), ("PDF", "*.pdf"),
                                                        ("SVG", "*.svg"), ("All Files", "*.*")])
        if fname:
            self.figure.savefig(fname, bbox_inches="tight")
            self.status.set(f"Saved plot to: {fname}")

    def ensure_symbols(self, vars_list):
        for v in vars_list:
            name = str(v)
            if name not in self.locals:
                self.locals[name] = Symbol(name)

    def list_functions(self):
        if not self.funcs:
            self.write("No functions defined yet.")
            return
        self.write("Defined functions:")
        for name, (args, lam) in self.funcs.items():
            self.write(f"  {name}({', '.join(str(a) for a in args)}) = {lam.expr}")

    def parse_locals(self):
        vars_syms = parse_vars(self.vars_entry.get().strip())
        vars_list = list(vars_syms) if isinstance(vars_syms, tuple) else [vars_syms] if vars_syms else []
        self.ensure_symbols(vars_list)
        for fname, (fargs, lam) in self.funcs.items():
            self.locals[fname] = lam
        for const in (pi, E, I):
            self.locals[str(const)] = const
        return vars_list

    # ---------- Plot helpers ----------
    def clear_plot(self):
        if not self.canvas:
            return
        self.figure.clf()
        self.ax = self.figure.add_subplot(111)
        self.canvas.draw_idle()

    def _apply_axes_cosmetics(self, title=None, xlabel=None, ylabel=None, legend=False):
        if not self.canvas:
            return
        if self.show_grid.get():
            self.ax.grid(True, linestyle="--", alpha=0.35)
        self.ax.axhline(0, linewidth=1, alpha=0.6)
        self.ax.axvline(0, linewidth=1, alpha=0.6)
        if title:
            self.ax.set_title(title)
        if xlabel:
            self.ax.set_xlabel(xlabel)
        if ylabel:
            self.ax.set_ylabel(ylabel)
        if legend:
            self.ax.legend(loc="best", framealpha=0.8)
        self.canvas.draw_idle()

    def _lamb(self, args, expr, backend="numpy"):
        # safer lambdify that tolerates SymPy functions -> NumPy where possible
        try:
            return lambdify(args, expr, backend)
        except Exception:
            # fallback to mpmath
            return lambdify(args, expr, "mpmath")

    def plot_line_from_expr(self, expr, x, xa=-10, xb=10, n=400, label=None):
        """Generic 1D plot of y = expr(x); if linear, annotate slope & intercepts."""
        if not self.canvas:
            self.write("Plot requested, but matplotlib not available.")
            return
        f = self._lamb(x, expr, "numpy")
        X = np.linspace(float(xa), float(xb), int(n))
        with np.errstate(all="ignore"):
            try:
                Y = f(X)
            except Exception:
                # fallback elementwise mpmath if needed
                fm = self._lamb(x, expr, "mpmath")
                Y = np.array([float(fm(xx)) for xx in X])
        Y = np.array(Y, dtype=float)
        (line,) = self.ax.plot(X, Y, label=label if label else None)

        # If linear, compute slope/intercepts
        try:
            P = Poly(expr, x)
            if P.total_degree() == 1:
                m = P.coeff_monomial(x)
                b = float(P.eval(0))
                slope = float(m)
                # annotate
                self.ax.annotate(f"m = {slope:.4g}", xy=(0.02, 0.98),
                                 xycoords="axes fraction", va="top", ha="left",
                                 bbox=dict(boxstyle="round", fc="w", alpha=0.7))
                self.ax.scatter([0], [b], zorder=5)
                self.ax.annotate(f"y-int = {b:.4g}", (0, b),
                                 textcoords="offset points", xytext=(6, 8))
                if slope != 0:
                    xint = -b/slope
                    self.ax.scatter([xint], [0], zorder=5)
                    self.ax.annotate(f"x-int = {xint:.4g}", (xint, 0),
                                     textcoords="offset points", xytext=(6, 8))
        except Exception:
            pass

        self._apply_axes_cosmetics(title=f"y = {expr}", xlabel=str(x), ylabel="y", legend=bool(label))

    # ---------- Function features ----------
    def define_functions_from_text(self, text):
        count = 0
        for line in [seg.strip() for seg in text.replace("\n", ";").split(";") if seg.strip()]:
            m = FUNC_DEF_RE.match(line)
            if not m:
                continue
            name = m.group(1)
            arg_names = [a.strip() for a in m.group(2).split(",") if a.strip()]
            rhs = m.group(3).strip()
            arg_symbols = [Symbol(a) for a in arg_names]
            ldict = dict(self.locals)
            for a in arg_symbols:
                ldict[str(a)] = a
            expr = parse_expr_safe(rhs, ldict)
            lam = Lambda(tuple(arg_symbols), expr)
            self.funcs[name] = (arg_symbols, lam)
            self.locals[name] = lam
            count += 1
            self.write(f"Defined {name}({', '.join(arg_names)}) = {expr}")
        if count == 0:
            self.write("No valid function definitions found.")

    # ---------- Automatic brain ----------
    def automatic(self, expr_text, params_text, vars_list, ldict):
        """
        Tries multiple strategies in a sensible order.
        1) Function definitions
        2) Multiple or single 'y = ...' lines → Plot 1D (with legend)
        3) Single implicit equation in x,y → Plot F(x,y)=0
        4) General equations / systems → Solve (with optional nsolve)
        5) Bare expression in one variable → Plot 1D
        6) Else: expand if power-ish; else simplify
        """
        # 1) Functions?
        has_def = any(FUNC_DEF_RE.match(seg.strip()) for seg in expr_text.replace("\n", ";").split(";") if seg.strip())
        if has_def:
            self.write("[Auto] Detected function definition(s).")
            self.define_functions_from_text(expr_text)
            return

        # Normalize lines split
        segments = [s.strip() for s in expr_text.replace("\n", ";").split(";") if s.strip()]

        # 2) y = f(x) possibly multiple
        y_lines = [LINE_Y_EQ_RE.match(seg) for seg in segments]
        if all(m is not None for m in y_lines):
            self.write("[Auto] Detected y = f(x) line(s). Plotting.")
            if not vars_list:
                vars_list = [Symbol("x")]
            x = vars_list[0]
            xa, xb, n, legend0 = parse_range_params(params_text, ldict, 'x', (-10, 10), 600)
            for i, m in enumerate(y_lines):
                rhs = parse_expr_safe(m.group(1), ldict)
                label = legend0 if legend0 else f"y{'' if len(y_lines)==1 else i+1}"
                self.plot_line_from_expr(rhs, x, xa, xb, n, label=label)
            return

        # 3) Implicit single equation in (x,y) → Plot
        if len(segments) == 1 and IMPLICIT_EQ_RE.match(segments[0]):
            # Try to plot F(x,y)=0
            try:
                L, R = [s.strip() for s in segments[0].split("=", 1)]
                F = parse_expr_safe(L, ldict) - parse_expr_safe(R, ldict)
                free = sorted(list(F.free_symbols), key=lambda s: str(s))
                if len(free) >= 2:
                    x = Symbol("x") if Symbol("x") in free else free[0]
                    y = Symbol("y") if Symbol("y") in free else free[1]
                    xa, xb, xn, ya, yb, yn, _ = parse_2d_params(params_text, ldict, (-5,5), 400, 20)
                    self._plot_implicit(F, x, y, xa, xb, xn, ya, yb, yn)
                    return
            except Exception as e:
                self.write(f"[Auto] Implicit plot failed: {e}. Trying other strategies…")

        # 4) Equations / systems → Solve
        if "=" in expr_text:
            try:
                eqs = parse_equations(expr_text, ldict)
                self.write("[Auto] Detected equation(s). Solving.")
                if vars_list:
                    self.write(f"Unknowns: {vars_list}")
                sols = solve(eqs, vars_list if vars_list else None, dict=True)
                if sols:
                    for i, sol in enumerate(sols, 1):
                        self.write(f"  {i}. {sol}")
                else:
                    self.write("No symbolic solution found.")
                if self.use_nsolve.get():
                    guess = parse_guess_from_params(params_text, ldict)
                    if guess and vars_list and len(guess) == len(vars_list):
                        f = [e.lhs - e.rhs for e in eqs]
                        sol_vec = nsolve(f, vars_list, guess)
                        self.write("nsolve:")
                        self.write(f"  {dict(zip(vars_list, sol_vec))}")
                return
            except Exception as e:
                self.write(f"[Auto] Solve attempt failed: {e}. Trying other strategies…")

        # 5) Bare expression in 1 variable → Plot
        try:
            expr = parse_expr_safe(expr_text, ldict)
            free = list(expr.free_symbols)
            if len(free) == 1:
                x = free[0]
                self.write(f"[Auto] Detected 1D expression in {x}. Plotting.")
                xa, xb, n, legend = parse_range_params(params_text, ldict, 'x', (-10, 10), 600)
                self.plot_line_from_expr(expr, x, xa, xb, n, label=legend)
                return
        except Exception:
            pass

        # 6) Algebraic: expand if power-ish, else simplify
        try:
            expr = parse_expr_safe(expr_text, ldict)
            txt = expr_text.replace(" ", "")
            looks_binomial = ("^" in txt or "**" in txt) and ("(" in txt and ")" in txt)
            if looks_binomial:
                self.write("[Auto] Looks like a power/binomial. Expanding.")
                self.write(f"Expanded:\n  {expand(expr)}")
            else:
                self.write("[Auto] Simplifying expression.")
                self.write(f"Simplified:\n  {simplify(expr)}")
            if self.numeric.get():
                try:
                    self.write("\nApproximation (evalf):")
                    self.write(f"  ≈ {expr.evalf()}")
                except Exception:
                    pass
            return
        except Exception as e:
            self.write(f"[Auto] Could not parse input: {e}")

    # ---------- Specialized plotters ----------
    def _plot_implicit(self, F, x, y, xa, xb, xn, ya, yb, yn):
        if not self.canvas:
            self.write("Plot requested, but matplotlib not available.")
            return
        self.ax.cla()
        f = self._lamb((x, y), F, "numpy")
        X = np.linspace(xa, xb, int(xn))
        Y = np.linspace(ya, yb, int(yn))
        XX, YY = np.meshgrid(X, Y)
        with np.errstate(all="ignore"):
            try:
                ZZ = f(XX, YY)
            except Exception:
                # fallback mpmath (slower)
                fm = self._lamb((x, y), F, "mpmath")
                ZZ = np.zeros_like(XX, dtype=float)
                for i in range(YY.shape[0]):
                    for j in range(XX.shape[1]):
                        try:
                            ZZ[i, j] = float(fm(XX[i, j], YY[i, j]))
                        except Exception:
                            ZZ[i, j] = np.nan
        CS = self.ax.contour(XX, YY, ZZ, levels=[0])
        CS.collections[0].set_label("F(x,y)=0")
        self._apply_axes_cosmetics(title=f"Implicit: {F}=0", xlabel=str(x), ylabel=str(y), legend=True)

    def _plot_parametric(self, Xexpr, Yexpr, t, ta, tb, n):
        if not self.canvas:
            self.write("Plot requested, but matplotlib not available.")
            return
        fX = self._lamb(t, Xexpr, "numpy")
        fY = self._lamb(t, Yexpr, "numpy")
        T = np.linspace(float(ta), float(tb), int(n))
        with np.errstate(all="ignore"):
            try:
                X = fX(T); Y = fY(T)
            except Exception:
                fmX = self._lamb(t, Xexpr, "mpmath")
                fmY = self._lamb(t, Yexpr, "mpmath")
                X = np.array([float(fmX(tt)) for tt in T])
                Y = np.array([float(fmY(tt)) for tt in T])
        self.ax.plot(X, Y, label="parametric")
        self._apply_axes_cosmetics(title="Parametric curve", xlabel="x(t)", ylabel="y(t)", legend=True)

    def _plot_polar(self, Rexpr, th, ta, tb, n):
        if not self.canvas:
            self.write("Plot requested, but matplotlib not available.")
            return
        # Evaluate r(theta)
        fr = self._lamb(th, Rexpr, "numpy")
        TH = np.linspace(float(ta), float(tb), int(n))
        with np.errstate(all="ignore"):
            try:
                R = fr(TH)
            except Exception:
                frm = self._lamb(th, Rexpr, "mpmath")
                R = np.array([float(frm(tt)) for tt in TH])
        X = R * np.cos(TH)
        Y = R * np.sin(TH)
        self.ax.plot(X, Y, label="polar")
        self._apply_axes_cosmetics(title="Polar curve", xlabel="x", ylabel="y", legend=True)

    def _plot_quiver(self, P, Q, x, y, xa, xb, xn, ya, yb, yn):
        if not self.canvas:
            self.write("Plot requested, but matplotlib not available.")
            return
        fP = self._lamb((x, y), P, "numpy")
        fQ = self._lamb((x, y), Q, "numpy")
        X = np.linspace(xa, xb, int(xn))
        Y = np.linspace(ya, yb, int(yn))
        XX, YY = np.meshgrid(X, Y)
        with np.errstate(all="ignore"):
            try:
                U = fP(XX, YY); V = fQ(XX, YY)
            except Exception:
                fmP = self._lamb((x, y), P, "mpmath")
                fmQ = self._lamb((x, y), Q, "mpmath")
                U = np.zeros_like(XX, dtype=float)
                V = np.zeros_like(YY, dtype=float)
                for i in range(YY.shape[0]):
                    for j in range(XX.shape[1]):
                        try: U[i, j] = float(fmP(XX[i, j], YY[i, j])); V[i, j] = float(fmQ(XX[i, j], YY[i, j]))
                        except Exception: U[i, j] = np.nan; V[i, j] = np.nan
        self.ax.quiver(XX, YY, U, V, pivot="mid", angles="xy", scale_units="xy")
        self._apply_axes_cosmetics(title="Vector field", xlabel=str(x), ylabel=str(y), legend=False)

    # ---------- Main ----------
    def run(self):
        self.output.delete("1.0", tk.END)
        if self.canvas:
            self.clear_plot()
        self.status.set("Working…")
        mode = self.mode.get()
        expr_text = self.expr_box.get("1.0", "end").strip()
        params_text = self.params_entry.get().strip()

        try:
            vars_list = self.parse_locals()
            ldict = self.locals

            # AUTOMATIC
            if mode == "Automatic":
                self.automatic(expr_text, params_text, vars_list, ldict)
                self.status.set("Done.")
                return

            # MANUAL MODES
            if mode == "Define function(s)":
                self.define_functions_from_text(expr_text)

            elif mode == "Call function / Evaluate":
                subs = {}
                if params_text:
                    for part in [p.strip() for p in params_text.split(",") if p.strip()]:
                        if "=" in part:
                            k, v = [s.strip() for s in part.split("=", 1)]
                            subs[Symbol(k)] = parse_expr_safe(v, ldict)
                expr = parse_expr_safe(expr_text, ldict)
                expr = expr.subs(subs) if subs else expr
                self.write(f"Expression:\n  {expr}")
                try:
                    val = expr.doit()
                except Exception:
                    val = expr
                self.write(f"Result:\n  {val}")
                if self.numeric.get():
                    try: self.write(f"Approx:\n  {val.evalf()}")
                    except Exception: self.write("Approx:\n  (n/a)")

            elif mode == "Solve (equation or system)":
                eqs = parse_equations(expr_text, ldict)
                self.write("Equations:")
                for e in eqs: self.write(f"  {e}")
                if vars_list: self.write(f"\nUnknowns: {vars_list}")
                sols = solve(eqs, vars_list if vars_list else None, dict=True)
                if sols:
                    self.write("\nSymbolic solutions:")
                    for i, sol in enumerate(sols, 1): self.write(f"  {i}. {sol}")
                else:
                    self.write("\nNo symbolic solution found.")
                if self.use_nsolve.get():
                    guess = parse_guess_from_params(params_text, ldict)
                    if guess and vars_list and len(guess) == len(vars_list):
                        f = [e.lhs - e.rhs for e in eqs]
                        sol_vec = nsolve(f, vars_list, guess)
                        self.write("\nNumeric nsolve solution:")
                        self.write(f"  {dict(zip(vars_list, sol_vec))}")

            elif mode == "Expand":
                expr = parse_expr_safe(expr_text, ldict); self.write(f"Expanded:\n  {expand(expr)}")
            elif mode == "Factor":
                expr = parse_expr_safe(expr_text, ldict); self.write(f"Factored:\n  {factor(expr)}")
            elif mode == "Simplify":
                expr = parse_expr_safe(expr_text, ldict); self.write(f"Simplified:\n  {simplify(expr)}")
            elif mode == "Partial Fractions (apart)":
                expr = parse_expr_safe(expr_text, ldict); self.write(f"Apart:\n  {apart(expr)}")

            elif mode == "Polynomial Tools":
                expr = parse_expr_safe(expr_text, ldict)
                if not vars_list: raise ValueError("Set VARIABLES (first is main polynomial variable).")
                x = vars_list[0]
                poly = Poly(expr, x)
                self.write(f"Poly in {x}:\n  {poly}")
                self.write(f"Degree: {poly.degree()}")
                try: self.write(f"Discriminant: {poly.discriminant()}")
                except Exception: self.write("Discriminant: (n/a)")
                try:
                    rs = roots(poly)
                    self.write("Roots (exact with multiplicities):")
                    for r, m in rs.items(): self.write(f"  {r}  (mult={m})")
                    # plot real roots as ticks if a 1D plot range is set
                except Exception:
                    self.write("Roots: (n/a)")

            elif mode == "Differentiate":
                expr = parse_expr_safe(expr_text, ldict)
                specs = parse_diff_params(params_text, vars_list)
                res = expr
                for vname, order in specs:
                    v = Symbol(vname)
                    res = diff(res, v, order)
                self.write(f"Derivative:\n  {res}")

            elif mode == "Integrate":
                expr = parse_expr_safe(expr_text, ldict)
                specs = parse_integral_params(params_text, ldict)
                if not specs:
                    if not vars_list: raise ValueError("Provide Params like 'x' or 'x:0:1', or set VARIABLES.")
                    specs = [(str(vars_list[0]), None)]
                res = expr
                for vname, lim in specs:
                    v = Symbol(vname)
                    res = integrate(res, v) if lim is None else integrate(res, (v, lim[0], lim[1]))
                self.write(f"Integral:\n  {res}")

            elif mode == "Limit":
                expr = parse_expr_safe(expr_text, ldict)
                vname, point, direction = parse_limit_params(params_text, ldict)
                v = Symbol(vname); res = sym_limit(expr, v, point, dir=direction)
                self.write(f"Limit ({vname}→{point}, dir='{direction}'):\n  {res}")

            elif mode == "Series (Taylor)":
                expr = parse_expr_safe(expr_text, ldict)
                vname, point, order = parse_series_params(params_text, ldict)
                v = Symbol(vname); s = series(expr, v, point, order).removeO()
                self.write(f"Series about {vname}={point} (order {order}):\n  {s}")

            elif mode == "Gradient":
                if not vars_list: raise ValueError("Set VARIABLES for gradient.")
                expr = parse_expr_safe(expr_text, ldict)
                grad = [diff(expr, v) for v in vars_list]
                self.write(f"Gradient wrt {vars_list}:\n  {Matrix(grad)}")

            elif mode == "Jacobian":
                if not vars_list: raise ValueError("Set VARIABLES for Jacobian.")
                vec = parse_expr_safe(expr_text, ldict)
                if not hasattr(vec, "__iter__"): raise ValueError("Jacobian input must be list/tuple.")
                F = Matrix(list(vec)); J = F.jacobian(vars_list)
                self.write(f"F = {F}"); self.write(f"Jacobian wrt {vars_list}:\n{J}")

            elif mode == "Hessian":
                if not vars_list: raise ValueError("Set VARIABLES for Hessian.")
                expr = parse_expr_safe(expr_text, ldict)
                H = Matrix([[diff(expr, vi, vj) for vj in vars_list] for vi in vars_list])
                self.write(f"Hessian wrt {vars_list}:\n{H}")

            elif mode == "Divergence":
                if not vars_list: raise ValueError("Set VARIABLES for Divergence.")
                vec = parse_expr_safe(expr_text, ldict)
                comps = list(vec) if hasattr(vec, "__iter__") else None
                if not comps or len(comps) != len(vars_list):
                    raise ValueError("Provide vector field list matching VARIABLES length.")
                div = sum(diff(comps[i], vars_list[i]) for i in range(len(vars_list)))
                self.write(f"Divergence of {Matrix(comps)} wrt {vars_list}:\n  {div}")

            elif mode == "Curl":
                if len(vars_list) != 3: raise ValueError("Curl requires 3 VARIABLES, e.g., x, y, z.")
                vec = parse_expr_safe(expr_text, ldict)
                comps = list(vec) if hasattr(vec, "__iter__") else None
                if not comps or len(comps) != 3: raise ValueError("Provide 3D vector field: [P, Q, R].")
                x, y, z = vars_list
                P, Q, R = comps
                curl_vec = Matrix([diff(R, y) - diff(Q, z),
                                   diff(P, z) - diff(R, x),
                                   diff(Q, x) - diff(P, y)])
                self.write(f"Curl of {Matrix(comps)}:\n  {curl_vec}")

            elif mode == "Plot 1D":
                expr = parse_expr_safe(expr_text, ldict)
                if not vars_list: raise ValueError("Set VARIABLES; first one is the x variable.")
                x = vars_list[0]
                xa, xb, n, legend = parse_range_params(params_text, ldict, 'x', (-5,5), 400)
                self.plot_line_from_expr(expr, x, xa, xb, n, label=legend)

            elif mode == "Plot 2D Contour":
                expr = parse_expr_safe(expr_text, ldict)
                if len(vars_list) < 2: raise ValueError("Set VARIABLES with at least two: x, y.")
                x, y = vars_list[:2]
                xa, xb, xn, ya, yb, yn, levels = parse_2d_params(params_text, ldict, (-3,3), 200, 20)
                f = self._lamb((x, y), expr, "numpy")
                X = np.linspace(xa, xb, int(xn)); Y = np.linspace(ya, yb, int(yn))
                XX, YY = np.meshgrid(X, Y)
                with np.errstate(all="ignore"):
                    try: Z = f(XX, YY)
                    except Exception:
                        fm = self._lamb((x, y), expr, "mpmath")
                        Z = np.zeros_like(XX, dtype=float)
                        for i in range(YY.shape[0]):
                            for j in range(XX.shape[1]):
                                try: Z[i, j] = float(fm(XX[i, j], YY[i, j]))
                                except Exception: Z[i, j] = np.nan
                self.ax.contour(X, Y, Z, levels=levels)
                self._apply_axes_cosmetics(title="Contour", xlabel=str(x), ylabel=str(y), legend=False)

            elif mode == "Plot 2D Surface (3D)*":
                if not HAVE_MPL:
                    self.write("Matplotlib 3D not available.")
                else:
                    from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
                    self.figure.clf()
                    ax3 = self.figure.add_subplot(111, projection='3d')
                    expr = parse_expr_safe(expr_text, ldict)
                    if len(vars_list) < 2: raise ValueError("Set VARIABLES with at least two: x, y.")
                    x, y = vars_list[:2]
                    xa, xb, xn, ya, yb, yn, _ = parse_2d_params(params_text, ldict, (-3,3), 80, 20)
                    f = self._lamb((x, y), expr, "numpy")
                    X = np.linspace(xa, xb, int(xn)); Y = np.linspace(ya, yb, int(yn))
                    XX, YY = np.meshgrid(X, Y)
                    with np.errstate(all="ignore"):
                        try: ZZ = f(XX, YY)
                        except Exception:
                            fm = self._lamb((x, y), expr, "mpmath")
                            ZZ = np.zeros_like(XX, dtype=float)
                            for i in range(YY.shape[0]):
                                for j in range(XX.shape[1]):
                                    try: ZZ[i, j] = float(fm(XX[i, j], YY[i, j]))
                                    except Exception: ZZ[i, j] = np.nan
                    ax3.plot_surface(XX, YY, ZZ, linewidth=0, antialiased=True)
                    ax3.set_xlabel(str(x)); ax3.set_ylabel(str(y)); ax3.set_zlabel("f")
                    ax3.set_title("Surface")
                    self.canvas.draw_idle()
                    self.write(f"Surface on [{xa},{xb}]x[{ya},{yb}]")

            elif mode == "Plot Implicit F(x,y)=0":
                if len(vars_list) < 2: raise ValueError("Set VARIABLES with at least two: x, y.")
                x, y = vars_list[:2]
                # Input can be "F(x,y)=0" or just "F(x,y)"
                if "=" in expr_text:
                    L, R = [s.strip() for s in expr_text.split("=", 1)]
                    F = parse_expr_safe(L, ldict) - parse_expr_safe(R, ldict)
                else:
                    F = parse_expr_safe(expr_text, ldict)
                xa, xb, xn, ya, yb, yn, _ = parse_2d_params(params_text, ldict, (-5,5), 400, 20)
                self._plot_implicit(F, x, y, xa, xb, xn, ya, yb, yn)

            elif mode == "Plot Parametric 2D":
                # Input: [x(t), y(t)] ; VARIABLES must contain t as first or include symbol 't'
                expr = parse_expr_safe(expr_text, ldict)
                if not hasattr(expr, "__iter__") or len(list(expr)) != 2:
                    raise ValueError("Provide a list [x(t), y(t)].")
                vec = list(expr)
                # choose t
                t = Symbol("t")
                if vars_list and vars_list[0] in (Symbol("t"),):
                    t = vars_list[0]
                ta, tb, n, _ = parse_range_params(params_text, ldict, 't', (0, 2*np.pi), 500)
                self._plot_parametric(vec[0], vec[1], t, ta, tb, n)

            elif mode == "Plot Polar":
                # Input: r(th); VARIABLES must include th or default to 'th'
                th = Symbol("th")
                if vars_list and vars_list[0] in (Symbol("th"), Symbol("theta")):
                    th = vars_list[0]
                Rexpr = parse_expr_safe(expr_text, ldict)
                ta, tb, n, _ = parse_range_params(params_text, ldict, 'th', (0, 2*np.pi), 500)
                self._plot_polar(Rexpr, th, ta, tb, n)

            elif mode == "Plot Quiver (vector field)":
                # Input: [P(x,y), Q(x,y)] ; VARIABLES: x, y
                if len(vars_list) < 2: raise ValueError("Set VARIABLES with at least two: x, y.")
                x, y = vars_list[:2]
                vec = parse_expr_safe(expr_text, ldict)
                if not hasattr(vec, "__iter__") or len(list(vec)) != 2:
                    raise ValueError("Provide [P(x,y), Q(x,y)].")
                P, Q = list(vec)
                xa, xb, xn, ya, yb, yn, _ = parse_2d_params(params_text, ldict, (-3,3), 20, 20)
                self._plot_quiver(P, Q, x, y, xa, xb, xn, ya, yb, yn)

            elif mode == "ODE: dsolve (symbolic)":
                funcname = "y"
                for seg in [s.strip() for s in params_text.replace("\n",";").split(";") if s.strip()]:
                    if seg.lower().startswith("function"):
                        _, v = seg.split("=",1); funcname = v.strip()
                if not vars_list: raise ValueError("Set VARIABLES; first is independent variable (e.g., t).")
                t = vars_list[0]
                y = Function(funcname)(t)
                ldict2 = dict(ldict); ldict2[funcname] = lambda arg: Function(funcname)(arg)
                ldict2[str(t)] = t; ldict2[str(y)] = y
                eqs = parse_equations(expr_text, ldict2)
                sol = dsolve(eqs[0])
                self.write(f"ODE solution:\n  {sol}")

            elif mode == "ODE: numeric (mpmath)":
                vec = parse_expr_safe(expr_text, ldict)
                if not hasattr(vec, "__iter__"): raise ValueError("Provide RHS list, e.g., [y, -x].")
                rhs_list = list(vec)
                if not vars_list or len(vars_list) < 1:
                    raise ValueError("Set VARIABLES with t first, then state variables (e.g., t, x, y).")
                t = vars_list[0]; states = vars_list[1:]
                if len(states) != len(rhs_list): raise ValueError("RHS dimension must match number of states.")
                # Parse numeric params
                def parse_time_params(ptext):
                    t0, t1, steps = 0.0, 10.0, 1000
                    y0 = None
                    for seg in [s.strip() for s in ptext.replace("\n",";").split(";") if s.strip()]:
                        low = seg.lower()
                        if low.startswith("tspan"):
                            _, r = seg.split(":",1)
                            lo, hi = [t.strip() for t in r.split(":")]
                            t0 = float(parse_expr_safe(lo, ldict))
                            t1 = float(parse_expr_safe(hi, ldict))
                        elif low.startswith("y0"):
                            _, v = seg.split(":",1)
                            arr = parse_expr_safe(v.strip(), ldict)
                            arr = list(arr) if hasattr(arr, "__iter__") else [float(arr)]
                            y0 = [float(val) for val in arr]
                        elif low.startswith("steps"):
                            _, v = seg.split("=",1)
                            steps = int(v.strip())
                    return t0, t1, steps, y0

                t0, t1, steps, y0 = parse_time_params(params_text)
                if y0 is None: raise ValueError("Provide y0: initial state vector, e.g., y0: [1, 0]")
                f = lambdify((t, states), rhs_list, "mpmath")
                dt = (t1 - t0) / steps
                traj = [y0[:]]
                times = [t0]
                yv = mp.matrix(y0)
                tt = t0
                for _ in range(steps):
                    k1 = mp.matrix(f(tt, list(yv)))
                    k2 = mp.matrix(f(tt + dt/2, list(yv + dt*k1/2)))
                    k3 = mp.matrix(f(tt + dt/2, list(yv + dt*k2/2)))
                    k4 = mp.matrix(f(tt + dt, list(yv + dt*k3)))
                    yv = yv + dt*(k1 + 2*k2 + 2*k3 + k4)/6
                    tt += dt
                    traj.append([float(val) for val in yv]); times.append(tt)
                self.write("Numeric ODE completed. Sample (t, y):")
                for i in range(0, len(times), max(1, len(times)//10)):
                    self.write(f"  t={times[i]:.4g}, y={traj[i]}")
                if self.canvas and traj and len(states) >= 1:
                    self.ax.plot(times, [p[0] for p in traj], label=str(states[0]))
                    self._apply_axes_cosmetics(title="ODE numeric", xlabel="t", ylabel=str(states[0]), legend=True)

            elif mode == "Optimization: critical points":
                if not vars_list: raise ValueError("Set VARIABLES for optimization.")
                expr = parse_expr_safe(expr_text, ldict)
                grad = [diff(expr, v) for v in vars_list]
                sols = solve(grad, vars_list, dict=True)
                if not sols: self.write("No stationary points found symbolically.")
                for i, sol in enumerate(sols, 1):
                    self.write(f"\nPoint {i}: {sol}")
                    H = Matrix([[diff(expr, vi, vj).subs(sol) for vj in vars_list] for vi in vars_list])
                    self.write(f"Hessian at point:\n{H}")
                    try:
                        evals = [ev.evalf() for ev in H.eigenvals().keys()]
                        self.write(f"Eigenvalues: {evals}")
                    except Exception:
                        self.write("Eigenvalues: (n/a)")

            elif mode == "Optimization: Lagrange (1 constraint)":
                if not vars_list: raise ValueError("Set VARIABLES for optimization.")
                expr = parse_expr_safe(expr_text, ldict)
                gtext = None
                for seg in [s.strip() for s in params_text.replace("\n",";").split(";") if s.strip()]:
                    if seg.lower().startswith("constraint"):
                        _, v = seg.split(":",1); gtext = v.strip()
                if not gtext: raise ValueError("Provide Params: constraint: g(x,...) = 0")
                if "=" not in gtext: raise ValueError("Constraint must be like g(...)=0")
                LHS, RHS = [s.strip() for s in gtext.split("=",1)]
                g = parse_expr_safe(LHS, ldict) - parse_expr_safe(RHS, ldict)
                lam = Symbol("λ")
                L = expr + lam*g
                eqs = [diff(L, v) for v in vars_list] + [g]
                sols = solve(eqs, vars_list + [lam], dict=True)
                if not sols: self.write("No Lagrange critical points found.")
                for i, sol in enumerate(sols, 1): self.write(f"  {i}. {sol}")

            elif mode == "Linear Algebra":
                mat = parse_expr_safe(expr_text, ldict)
                if not hasattr(mat, "__iter__"): raise ValueError("Provide a matrix like [[1,2],[3,4]].")
                M = Matrix(list(mat))
                ops = "all"
                for seg in [s.strip() for s in params_text.replace("\n",";").split(";") if s.strip()]:
                    if seg.lower().startswith("ops"):
                        _, v = seg.split("=",1); ops = v.strip().lower()
                self.write(f"Matrix:\n{M}")
                if ops=="all" or "rref" in ops:
                    R, piv = M.rref(); self.write(f"RREF:\n{R}\nPivots: {piv}")
                if ops=="all" or "rank" in ops: self.write(f"Rank: {M.rank()}")
                if ops=="all" or "det" in ops:
                    try: self.write(f"Determinant: {M.det()}")
                    except Exception: self.write("Determinant: (n/a)")
                if ops=="all" or "inv" in ops:
                    try: self.write(f"Inverse:\n{M.inv()}")
                    except Exception: self.write("Inverse: (n/a)")
                if ops=="all" or "eigs" in ops:
                    try:
                        self.write("Eigenvalues / vectors:")
                        for val, mult in M.eigenvals().items():
                            self.write(f"  λ={val} (mult={mult})")
                        for eig in M.eigenvects():
                            self.write(f"  λ={eig[0]} vecs={eig[2]}")
                    except Exception:
                        self.write("Eigen-data: (n/a)")
                if ops=="all" or "sv" in ops:
                    try: self.write(f"Singular values: {M.singular_values()}")
                    except Exception: self.write("Singular values: (n/a)")

            elif mode == "Complex Residue":
                expr = parse_expr_safe(expr_text, ldict)
                if not vars_list: raise ValueError("Set VARIABLES; first is complex variable (e.g., z).")
                zsym = vars_list[0]
                # parse at=point
                point = None
                for seg in [s.strip() for s in params_text.replace("\n",";").split(";") if s.strip()]:
                    if seg.lower().startswith("at"):
                        _, v = seg.split("=",1); point = parse_expr_safe(v.strip(), ldict)
                if point is None: raise ValueError("Params need at=point (e.g., at=0).")
                res_val = try_sympy_residue(expr, zsym, point)
                self.write(f"Residue at {zsym}={point}:\n  {res_val}")

            elif mode == "Logic: truth table & simplify":
                expr = parse_expr_safe(expr_text, ldict)
                if not vars_list: raise ValueError("Set VARIABLES for boolean variables.")
                self.write("Truth table:")
                from itertools import product
                syms = vars_list
                header = " | ".join([str(s) for s in syms] + [str(expr)])
                self.write(header)
                for vals in product([False, True], repeat=len(syms)):
                    val_expr = expr
                    for s, v in zip(syms, vals):
                        val_expr = val_expr.subs({s: v})
                    self.write(" | ".join([("T" if v else "F") for v in vals] + [("T" if bool(val_expr) else "F")]))
                self.write(f"\nSimplified (DNF): {simplify_logic(expr, form='dnf')}")
                self.write(f"Simplified (CNF): {simplify_logic(expr, form='cnf')}")

            elif mode == "Number Theory":
                op = "factorint"
                for seg in [s.strip() for s in params_text.replace("\n",";").split(";") if s.strip()]:
                    if seg.lower().startswith("op"):
                        _, v = seg.split("=",1); op = v.strip().lower()
                parts = [p.strip() for p in expr_text.replace("\n",",").split(",") if p.strip()]
                ints = [int(str(parse_expr_safe(p, ldict))) for p in parts]
                if op == "gcd":
                    g = 0
                    for n in ints: g = gcd(g, n)
                    self.write(f"gcd({ints}) = {g}")
                elif op == "lcm":
                    L = 1
                    for n in ints: L = lcm(L, n)
                    self.write(f"lcm({ints}) = {L}")
                elif op == "prime":
                    from sympy import isprime, nextprime
                    self.write("\n".join([f"{n}: {'prime' if isprime(n) else 'composite'}, nextprime={nextprime(n)}" for n in ints]))
                else:
                    self.write("\n".join([f"{n}: {factorint(n)}" for n in ints]))

            # numeric approx (best effort for expression-like results)
            if self.numeric.get() and mode not in {
                "Automatic", "Define function(s)", "Plot 1D", "Plot 2D Contour", "Plot 2D Surface (3D)*",
                "Plot Implicit F(x,y)=0", "Plot Parametric 2D", "Plot Polar", "Plot Quiver (vector field)",
                "ODE: numeric (mpmath)", "Logic: truth table & simplify", "Number Theory", "Linear Algebra"
            }:
                self.write("\nApproximation (evalf):")
                try:
                    last_line = self.output.get("1.0", "end").strip().splitlines()[-1]
                    val = parse_expr_safe(last_line, ldict)
                    self.write(f"  ≈ {val.evalf()}")
                except Exception:
                    self.write("  (n/a)")

            self.status.set("Done.")
        except (ValueError, SympifyError) as e:
            messagebox.showerror("Input Error", str(e))
            self.status.set("Error.")
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")
            self.status.set("Error.")

if __name__ == "__main__":
    app = MathLab()
    app.mainloop()
