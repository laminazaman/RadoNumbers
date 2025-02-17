from divitems import DivItems
from divisibility import Divisibility
from constraint import Constraint
import sympy as sp

class Interval:
    def __init__(self, symbols, interval, divitems, subs, constraint=None, constraints=None):
        self.interval = interval
        self.divitems = divitems
        self.symbols = symbols
        self.subs = subs
        self.min, self.max = self.get_min_max()
        self.constraint = constraint
        self.constraints = constraints

    def set_constraint(self, function, ranges):
        self.constraint = Constraint(function, ranges)

    def get_interval(self):
        return [self.interval.start, self.interval.end]
    
    def get_divitems(self):
        return self.divitems.get()

    def get(self):
        return {
            'interval': self.get_interval(),
            'divitems': self.get_divitems(),
            'constraint': None if self.constraint == None else self.constraint.get(),
            'monotonic': 
                self.is_lb_monotonic_increasing(self.symbols) 
                and self.is_ub_monotonic_increasing(self.symbols),
            'min': self.get_min(),
            'max': self.get_max() 
        }

    def is_lb_monotonic_increasing(self, vars):
        monotonic = True
        for v in vars:
            f_prime = sp.diff(self.interval.start, v)
            f_monotonic_increasing = sp.simplify(f_prime) >= 0
            monotonic = monotonic & f_monotonic_increasing
        return monotonic

    def is_ub_monotonic_increasing(self, vars):
        monotonic = True
        for v in vars:
            f_prime = sp.diff(self.interval.end, v)
            f_monotonic_increasing = sp.simplify(f_prime) >= 0
            monotonic = monotonic & f_monotonic_increasing
        return monotonic

    def get_min_max(self):
        """Finds symbolic min and max satisfying divisibility conditions."""
        L = self.interval.start
        U = self.interval.end
        
        must_divide = [item[0] for item in self.get_divitems() if item[1] == True]
        must_not_divide = [item[0] for item in self.get_divitems() if item[1] == False]

        # Compute symbolic LCM of required divisors
        M = sp.lcm(must_divide)

        # Define k as a symbolic integer
        k = sp.symbols('k', integer=True)

        # Compute the first multiple of M greater than or equal to L (symbolically)
        min_elem_expr = sp.ceiling(L / M) * M

        # Ensure min_elem_expr is NOT divisible by elements in must_not_divide
        min_elem = sp.simplify(min_elem_expr)
        for n in must_not_divide:
            if sp.Mod(min_elem, n) == 0:
                min_elem += M

        # Compute the last multiple of M less than or equal to U (symbolically)
        max_elem_expr = sp.floor(U / M) * M
        
        # Ensure max_elem_expr is NOT divisible by elements in must_not_divide
        max_elem = sp.simplify(max_elem_expr)
        for n in must_not_divide:
            if sp.Mod(max_elem, n) == 0:
                max_elem -= M

        return sp.simplify(min_elem), sp.simplify(max_elem)

    def get_max(self):
        return self.max

    def get_min(self):
        return self.min

    def below_the_lower_bound(self, z):
        texp = sp.simplify(self.interval.start - z)
        if texp.subs(self.subs) >= 0:
            return True
        return False

    def above_the_upper_bound(self, z):
        texp = sp.simplify(z - self.interval.end)
        if texp.subs(self.subs) >= 0:
            return True
        return False

    def contains(self, z):
        L = self.interval.start
        U = self.interval.end
        
        must_divide = [item[0] for item in self.get_divitems() if item[1] == True]
        must_not_divide = [item[0] for item in self.get_divitems() if item[1] == False]

        # Check if z is inside the interval [L, U]
        in_range = sp.And(
            sp.Not(self.below_the_lower_bound(z)), 
            sp.Not(self.above_the_upper_bound(z)))

        # Check if z is divisible by all numbers in must_divide
        div_conditions = [sp.Mod(z, d) == 0 for d in must_divide]

        # Check if z is NOT divisible by any number in must_not_divide
        nondiv_conditions = [sp.Mod(z, n) != 0 for n in must_not_divide]

        # Combine all conditions
        membership_condition = sp.And(in_range, *div_conditions, *nondiv_conditions)

        constraint_satisfied = self.constraint.satisfied(z.subs(self.subs))        

        # Simplify the logical expression
        return sp.simplify(membership_condition)

