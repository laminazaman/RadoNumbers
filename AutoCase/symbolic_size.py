import sympy as sp
from itertools import chain, combinations

def simplify_floor_by_degree(expr, a):
    if not expr.has(sp.floor):
        return expr

    def condition(e):
        return isinstance(e, sp.floor)

    def replacement(e):
        arg = sp.simplify(e.args[0])
        p, q = arg.as_numer_denom()

        if not p.has(a) and not q.has(a):
            return sp.floor(arg)

        deg_p = sp.degree(p, gen=a)
        deg_q = sp.degree(q, gen=a)

        if deg_p < deg_q:
            leading_p = sp.Poly(p, a).LC()
            leading_q = sp.Poly(q, a).LC()

            sign_at_inf = sp.sign(leading_p / leading_q)

            if sign_at_inf == 1:
                return sp.Integer(0)
            elif sign_at_inf == -1:
                return sp.Integer(-1)

        return e
    return expr.replace(condition, replacement)


def substitute_by_name(expr, replacements):
    return expr.xreplace({
        s: sp.sympify(val)
        for s in expr.atoms(sp.Symbol)
        if s.name in replacements
        for val in [replacements[s.name]]
    })


def symbolic_set(iterable):
    result = []
    for item in iterable:
        if not any(item == existing for existing in result):
            result.append(item)
    return set(result)


def powerset(iterable):
    """Generate all non-empty subsets of a list"""
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(1, len(s)+1))


class SymbolicSize:
    def __init__(self, interval):
        self.interval = interval

    def compute(self):
        size = (self._format_based_size() if self._has_format()
                else self._regular_interval_size())

        size = self._subtract_excluded_intervals(size)
        return sp.simplify(size)
        
    def _has_format(self):
        return (self.interval.format_expr and
                self.interval.format_vars and
                self.interval.format_ranges)

    def _format_based_size(self):
        vars_order = list(self.interval.format_vars)

        def nested_sum(depth=0):
            if depth == len(vars_order):
                return 1
            var = vars_order[depth]
            lo, hi = self._clean_expr(self.interval.format_ranges[var])
            return sp.Sum(nested_sum(depth + 1), (var, lo, hi))

        try:
            return sp.simplify(nested_sum().doit())
        except Exception:
            return nested_sum()

    def _regular_interval_size(self):
        if self.interval.lower is None or self.interval.upper is None:
            return None

        base = sp.ceiling(self.interval.lower)
        top = sp.floor(self.interval.upper)

        if self.interval.must_divide:
            lcm = sp.lcm(self.interval.must_divide)
            count_div = self._count_multiples(base, top, lcm)
        else:
            lcm = 1
            count_div = top - base + 1

        if self.interval.must_not_divide:
            count_excl = self._inclusion_exclusion_exclusions(base, top, lcm, self.interval.must_not_divide)
        else:
            count_excl = 0

        return sp.simplify(count_div + count_excl)

    def _count_multiples(self, lo, hi, d):
        return sp.floor(hi / d) - sp.floor((lo - 1) / d)

    def _inclusion_exclusion_exclusions(self, lo, hi, base_lcm, exclusions):
        total = 0
        for subset in powerset(exclusions):
            lcm_excl = sp.lcm([base_lcm] + list(subset))
            sign = (-1) ** len(subset)
            total += sign * self._count_multiples(lo, hi, lcm_excl)
        return total

    def _clean_expr(self, bound_tuple):
        lo = sp.sympify(bound_tuple[0])
        hi = sp.sympify(bound_tuple[1])
        return (
            lo.replace(sp.floor, lambda x: x) if lo.has(sp.floor) else lo,
            hi.replace(sp.floor, lambda x: x) if hi.has(sp.floor) else hi,
        )

    def _subtract_excluded_intervals(self, size):
        if hasattr(self.interval, 'excluded_intervals'):
            for excl in self.interval.excluded_intervals:
                excl_size = SymbolicSize(excl).compute()
                if excl_size is not None:
                    size -= excl_size
        return size
