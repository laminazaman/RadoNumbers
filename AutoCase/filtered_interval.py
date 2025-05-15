import sympy as sp
import z3 as z3
from z3_solver import Z3Solver

class FilteredInterval:
    def __init__(self, symbols, assumptions=[], bounds=[None, None], filters=[], excluded_intervals=[]):
        self.symbols = symbols
        self.assumptions = assumptions
        self.lower = bounds[0]
        self.upper = bounds[1]
        self.must_divide = []
        self.must_not_divide = []
        self.format_expr = None
        self.format_vars = []
        self.format_ranges = {}
        self.constraints = []
        self.excluded_intervals = excluded_intervals

    def get(self):
        return {
            'symbols': self.symbols,
            'assumptions': self.assumptions,
            'lower': self.lower,
            'upper': self.upper,
            'must_divide': self.must_divide,
            'must_not_divide': self.must_not_divide,
            'format_expr': self.format_expr,
            'format_vars': self.format_vars,
            'format_ranges': self.format_ranges,
            'constraints': self.constraints
        }

        # Concise lambda-style filters
        z = sp.Symbol('z', integer=True)
        for f in filters:
            try:
                self.add_constraint(f(z))
            except:
                raise ValueError("Invalid filter passed to FilteredInterval")

    # ------------------------ Setup ------------------------

    def add_symbol(self, symbol):
        if symbol not in self.symbols:
            self.symbols.append(symbol)

    def set_assumptions(self, assumptions):
        self.assumptions = assumptions

    def get_symbols(self):
        return self.symbols

    def set_bounds(self, lower, upper):
        self.lower = sp.sympify(lower)
        self.upper = sp.sympify(upper)

    def get_bounds(self):
        return self.lower, self.upper

    def add_must_divide(self, d):
        self.must_divide.append(sp.sympify(d))

    def add_must_not_divide(self, d):
        self.must_not_divide.append(sp.sympify(d))

    def set_format_expression(self, expr, variables=[]):
        self.format_expr = sp.sympify(expr)
        self.format_vars = variables

    def set_format_ranges(self, ranges_dict):
        self.format_ranges = ranges_dict

    def add_constraint(self, condition):
        self.constraints.append(sp.sympify(condition))

    def add_excluded_interval(self, interval):
        self.excluded_intervals.append(interval)

    def set_excluded_intervals(self, intervals):
        self.excluded_intervals = intervals

    # ------------------------- Disjointness -----------------------------
    def is_disjoint(self, other):
        z = sp.Symbol('z', integer=True)
        all_vars = list(set(self.symbols + other.symbols + [z]))

        # Add format symbols from self and other
        fmt_syms_self = {v: sp.Symbol(f"_fmt_{str(v)}", integer=True) for v in self.format_vars}
        fmt_syms_other = {v: sp.Symbol(f"_fmt_{str(v)}", integer=True) for v in other.format_vars}
        all_vars.extend(fmt_syms_self.values())
        all_vars.extend(fmt_syms_other.values())

        # Substitute map for constraints
        fmt_subs_self = {v if isinstance(v, sp.Symbol) else sp.Symbol(v): fmt_syms_self[v] for v in self.format_vars}
        fmt_subs_other = {v if isinstance(v, sp.Symbol) else sp.Symbol(v): fmt_syms_other[v] for v in other.format_vars}

        # Start constraints
        constraints = list(self.assumptions + other.assumptions)
        if self.lower is not None:
            constraints.append(z >= self.lower)
        if self.upper is not None:
            constraints.append(z <= self.upper)

        if other.lower is not None:
            constraints.append(z >= other.lower)
        if other.upper is not None:
            constraints.append(z <= other.upper)

        # Divisibility constraints
        for d in self.must_divide:
            constraints.append(sp.Mod(z, d) == 0)
        for n in self.must_not_divide:
            constraints.append(sp.Mod(z, n) != 0)
        for d in other.must_divide:
            constraints.append(sp.Mod(z, d) == 0)
        for n in other.must_not_divide:
            constraints.append(sp.Mod(z, n) != 0)

        # Format expressions and ranges from self
        if self.format_expr and self.format_vars and self.format_ranges:
            fz_self = self.format_expr.subs(fmt_subs_self)
            constraints.append(sp.Eq(z, fz_self))
            for v, (lo, hi) in self.format_ranges.items():
                vi = fmt_syms_self[v]
                lo = sp.sympify(lo).subs(fmt_subs_self)
                hi = sp.sympify(hi).subs(fmt_subs_self)
                if hasattr(lo, 'has') and lo.has(sp.floor):
                    lo = lo.replace(sp.floor, lambda x: x)
                if hasattr(hi, 'has') and hi.has(sp.floor):
                    hi = hi.replace(sp.floor, lambda x: x)
                constraints.append(vi >= lo)
                constraints.append(vi <= hi)

        # Format expressions and ranges from other
        if other.format_expr and other.format_vars and other.format_ranges:
            fz_other = other.format_expr.subs(fmt_subs_other)
            constraints.append(sp.Eq(z, fz_other))
            for v, (lo, hi) in other.format_ranges.items():
                vi = fmt_syms_other[v]
                lo = sp.sympify(lo).subs(fmt_subs_other)
                hi = sp.sympify(hi).subs(fmt_subs_other)
                if hasattr(lo, 'has') and lo.has(sp.floor):
                    lo = lo.replace(sp.floor, lambda x: x)
                if hasattr(hi, 'has') and hi.has(sp.floor):
                    hi = hi.replace(sp.floor, lambda x: x)
                constraints.append(vi >= lo)
                constraints.append(vi <= hi)

        # Apply substitutions to all constraints
        constraints = [
            c.subs(fmt_subs_self).subs(fmt_subs_other) if isinstance(c, sp.Basic) else c
            for c in constraints
        ]

        solver = Z3Solver(vars=all_vars, constraints=constraints)
        check = solver.check()
        return solver.model(check) is None
