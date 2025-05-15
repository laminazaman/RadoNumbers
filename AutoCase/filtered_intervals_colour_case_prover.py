import sympy as sp
from itertools import product
from filtered_interval import FilteredInterval
from z3_solver import Z3Solver
from symbolic_size import SymbolicSize, simplify_floor_by_degree, symbolic_set, substitute_by_name
from sympy import Basic

import z3 as z3
import pprint
import time

class FilteredIntervalsColorCaseProver:
    def __init__(self):
        self.intervals = dict()
        self.colouring = dict()
        self.equation = list()
        self.statement = ""
        self.assumptions = []
    
    def get(self):
        return {
            'statement': self.statement,
            'intervals': {interval: self.intervals[interval].get() for interval in self.intervals},
            'colouring': self.colouring,
            'equation': self.equation,
            'assumptions': self.assumptions
        }

    def set_statement(self, statement):
        self.statement = statement

    def set_equation(self, eq):
        self.equation = eq

    def set_assumptions(self, assumptions):
        self.assumptions = assumptions

    def add_interval(self, name, interval: FilteredInterval):
        interval.set_assumptions(self.assumptions)
        self.intervals[name] = interval

    def add_interval_to_colour(self, c, name):
        if c not in self.colouring:
            self.colouring[c] = []
        self.colouring[c].append(name)

    def add_intervals_to_colour(self, c, names):
        for name in names:
            self.add_interval_to_colour(c, name)

    def generate_variable_containments(self, m, t):
        return list(product(range(t), repeat=m-1))

    def generate_colour_cases(self, col):
        m = len(self.equation)
        t = len(self.colouring[col])
        containments = self.generate_variable_containments(m, t)
        cases = []
        for c in containments:
            lhs_intervals = [self.colouring[col][c[i]] for i in range(m - 1)]
            earliest_interval = sorted(lhs_intervals)[0]
            z_intervals = [name for name in self.colouring[col]]
            cases.append([tuple(lhs_intervals), z_intervals])
        return cases

    def check_partition(self, n):
        if not self.covers_the_overall_interval(n):
            print("Partition does not seem to be correct!")
            exit(0)
        else:
            print("Partition is correct!")

    def generate_cases(self, n):        
        return {c: self.generate_colour_cases(c) for c in self.colouring}

    ########################################################################
    def extract_divisibility_tags(self, lhs_intervals, target):
        div_tags = []
        for i, interval in enumerate(lhs_intervals):
            for d in self.intervals[interval].must_divide:
                div_tags.append(('divides', d, f"x_{i+1}"))
            for d in self.intervals[interval].must_not_divide:
                div_tags.append(('not_divides', d, f"x_{i+1}"))

        for d in self.intervals[target].must_divide:
            div_tags.append(('divides', d, f"x_{len(lhs_intervals)+1}"))
        for d in self.intervals[target].must_not_divide:
            div_tags.append(('not_divides', d, f"x_{len(lhs_intervals)+1}"))
        return div_tags

    def parse_sympy_expr(self, expr, z3_vars):
        if isinstance(expr, sp.Basic):
            # Add any missing symbols as Z3 variables
            for sym in expr.free_symbols:
                name = str(sym)
                if name not in z3_vars:
                    z3_vars[name] = z3.Int(name)

            expr_str = str(expr)
            return eval(expr_str, {}, z3_vars)

        elif isinstance(expr, int):
            return z3.IntVal(expr)

        elif isinstance(expr, z3.ExprRef):
            return expr

        raise ValueError(f"Unsupported expression type: {type(expr)} — {expr}")


    def check_equation_with_div_tags_sympy(self, sympy_eq, div_tags, extra_assumptions=None):
        solver = z3.Solver()
        z3_vars = {}

        def get_z3_var(name):
            if name not in z3_vars:
                z3_vars[name] = z3.Int(name)
            return z3_vars[name]

        # Add divisibility constraints
        for tag, d_expr, var_name in div_tags:
            x = get_z3_var(var_name)
            d = self.parse_sympy_expr(d_expr, z3_vars)

            if tag == 'divides':
                k = z3.Int(f'k_{var_name}')
                solver.add(k > 0, x == d * k)

            elif tag == 'not_divides':
                k = z3.Int(f'k_{var_name}')
                solver.add(z3.ForAll([k], z3.And(k>0, x != d * k)))
                

            else:
                raise ValueError(f"Unknown tag: {tag}")

        # Add equation
        lhs = self.parse_sympy_expr(sympy_eq.lhs, z3_vars)
        rhs = self.parse_sympy_expr(sympy_eq.rhs, z3_vars)
        solver.add(lhs == rhs)

        # Optional assumptions
        if extra_assumptions:
            for asm in extra_assumptions:
                solver.add(asm)
        solver.set("timeout", 10000)
        result = solver.check()
        model = solver.model() if result == z3.sat else None
        return result, model, solver
    
    def generate_proof(self, colour_cases):
        start = time.time()
        current_time = time.time()
        counts = {'SAT': 0, 'UNSAT': 0, 'UNKNOWN': 0}

        output = {}
        output_verified = True
        z = sp.Symbol('z', integer=True)
        case_number = 0
        for colour_case, cases in colour_cases.items():
            output[colour_case] = []

            for case in cases:
                print(f"Case {case_number + 1} — Intervals for LHS variables: {case[0]}, RHS interval candidates: {case[1]}")                
                lhs_intervals = case[0]
                rhs_interval_names = case[1]

                lhs_vars = [sp.Symbol(f"x_{i+1}", integer=True, positive=True) for i in range(len(lhs_intervals))]
                rhs_var = sp.Symbol(f"x_{len(lhs_intervals)+1}", integer=True, positive=True)

                lhs_bounds = [self.intervals[name].get_bounds() for name in lhs_intervals]
                lhs_min = sum(self.equation[i] * lhs_bounds[i][0] for i in range(len(lhs_bounds)))
                lhs_max = sum(self.equation[i] * lhs_bounds[i][1] for i in range(len(lhs_bounds)))

                rhs_coeff = self.equation[-1]
                z_min = sp.simplify(lhs_min / rhs_coeff)
                z_max = sp.simplify(lhs_max / rhs_coeff)
                target_count = 0                
                for target in rhs_interval_names:
                    print("############################################################################")
                    print(f"Case {case_number + 1}.{target_count + 1} — Intervals for LHS variables: {case[0]}, RHS candidate: {target}")
                    target_count += 1
                    bound_contradiction = False

                    interval = self.intervals[target]
                    eq_expr = sum(self.equation[i] * lhs_vars[i] for i in range(len(lhs_vars))) - self.equation[-1] * rhs_var
                    eq = sp.Eq(eq_expr, 0)
                    div_tags = self.extract_divisibility_tags(lhs_intervals, target)
                    
                    if len(div_tags)>0:                        
                        res, model, solver = self.check_equation_with_div_tags_sympy(eq, div_tags)
                        if res == z3.unsat:
                            print('INPUT CONSTRAINTS in Z3:')
                            print("----------------------------------------------------------------------------")
                            pprint.pprint(solver.assertions())
                            print()
                            print(f"Z3 OUTPUT: UNSAT => No integer solution exists")
                            counts['UNSAT'] += 1
                            print(f"Case time: {time.time()-current_time:0.2f}; Elapsed time: {time.time()-start:0.2f}; Current counts: {counts}")
                            current_time = time.time()
                            print("############################################################################")
                            continue
                            
                    assumptions = self.assumptions
                    constraints = self.get_all_constraints(lhs_vars, lhs_intervals, rhs_var, target)
                    constraints.extend([rhs_var >= z_min, rhs_var <= z_max])
                    vars = Z3Solver.extract_all_symbols(constraints)
                            
                    z3solver = Z3Solver(vars, constraints=[eq] + assumptions + constraints, div_tags=div_tags)
                    print('INPUT CONSTRAINTS in Z3:')
                    print("----------------------------------------------------------------------------")
                    pprint.pprint(z3solver.constraints)
                    print()
                            
                    result = z3solver.check()
                    if result == z3.unsat:
                        counts['UNSAT'] += 1
                        print(f"Z3 OUTPUT: UNSAT => {rhs_var} not in {target}")
                    elif result == z3.sat:
                        counts['SAT'] += 1
                        output_verified = False
                        pprint.pprint(z3solver.model(result))
                    else: 
                        counts['UNKNOWN'] += 1

                    print(f"Case time: {time.time()-current_time:0.2f}; Elapsed time: {time.time()-start:0.2f}; Current counts: {counts}")
                    current_time = time.time()
                    print("############################################################################")

                case_number += 1
                print()
        end = time.time()
        print(f"\nAll cases led to contradiction?: {output_verified}")
        print(f"\nTotal proof-generation time: {end-start:0.2f}")
        print(f"\nTotal proof-subcases result summary: {counts}")

    def get_constraints_for_an_interval(self, i, var, name):
        constraints = []
        interval = self.intervals[name]
        # Constraints for bounds
        lo, hi = interval.get_bounds()
        sympy_var = sp.Symbol(str(var), integer=True)
        constraints.append(sp.GreaterThan(sympy_var, lo, evaluate=False))
        constraints.append(sp.LessThan(sympy_var, hi, evaluate=False))        

        # Constraints for divisibility properties
        for d in interval.must_divide:
            constraints.append(('divides', d, sympy_var, interval.get_bounds()[1]))
        for d in interval.must_not_divide:
            constraints.append(('not_divides', d, sympy_var, interval.get_bounds()[1]))

        # Format constraints
        substitutions = {}
        new_vars = []
        if interval.format_expr and interval.format_vars and interval.format_ranges:
            fmt_syms = {v: sp.Symbol(f"{v}_{i}", integer=True) for v in interval.format_vars}
            new_vars.extend(fmt_syms.values())
            substitutions[var] = interval.format_expr.subs(fmt_syms)
            for v in interval.format_vars:
                lo_expr, hi_expr = map(sp.sympify, interval.format_ranges[v])
                lo = lo_expr.subs(fmt_syms)
                hi = hi_expr.subs(fmt_syms)
                lo = lo.replace(sp.floor, lambda y: sp.simplify(y)) if hasattr(lo, 'has') and lo.has(sp.floor) else lo
                hi = hi.replace(sp.floor, lambda y: sp.simplify(y)) if hasattr(hi, 'has') and hi.has(sp.floor) else hi
                constraints += [
                    sp.Ge(fmt_syms[v], lo, evaluate=False),
                    sp.Le(fmt_syms[v], hi, evaluate=False)
                ]

            if interval.format_expr:
                format_subst = interval.format_expr.subs(fmt_syms)
                constraints.append(sp.Eq(var, format_subst, evaluate=False))

        # Exclusion constraints
        if interval.excluded_intervals:    
            for excl in interval.excluded_intervals:
                z = sp.Symbol(str(var), integer=True)
                if excl.format_expr and excl.format_vars:
                    # Build format substitution for excluded interval
                    fmt_syms = {v: sp.Symbol(f"excl_{v}_{i}", integer=True) for v in excl.format_vars}
                    format_val = excl.format_expr.subs(fmt_syms)
                    eq = sp.Ne(z, format_val)
                    constraints.append(eq)

                     # Also add bounds on format vars (to ensure they generate real points)
                    for v, (lo, hi) in excl.format_ranges.items():
                        vi = fmt_syms[v]
                        lo = sp.sympify(lo).subs(fmt_syms)
                        hi = sp.sympify(hi).subs(fmt_syms)
                        lo = lo.replace(sp.floor, lambda y: sp.simplify(y)) if hasattr(lo, 'has') and lo.has(sp.floor) else lo
                        hi = hi.replace(sp.floor, lambda y: sp.simplify(y)) if hasattr(hi, 'has') and hi.has(sp.floor) else hi

                        constraints.append(vi >= lo)
                        constraints.append(vi <= hi)
                else:
                    lo, hi = excl.get_bounds()
                    constraints.append(sp.Or(z < lo, z > hi))
        else:
            substitutions[var] = var

        return constraints

    def get_all_constraints(self, lhs_vars, lhs_intervals, rhs_var, rhs_interval):
        all_constraints = []
        for i, var in enumerate(lhs_vars):
            all_constraints = all_constraints + self.get_constraints_for_an_interval(i, lhs_vars[i], lhs_intervals[i])
        all_constraints = all_constraints + self.get_constraints_for_an_interval(len(lhs_vars), rhs_var, rhs_interval)
                
        return all_constraints
        
    def covers_the_overall_interval(self, n):
        # Check symbolic disjointness
        disjoint = True
        names = list(self.intervals.keys())
        for i in range(len(names)):
            for j in range(i + 1, len(names)):
                iv1 = self.intervals[names[i]]
                iv2 = self.intervals[names[j]]
                if not iv1.is_disjoint(iv2):
                    disjoint = False
                    print(f"{names[i]} and {names[j]} are not disjoint.")
                else:
                    pass

        sizes = []

        for name in self.intervals:
            expr = SymbolicSize(self.intervals[name]).compute()
            sizes.append(expr)
        
        a = sp.Symbol('a', integer=True)
        b = sp.Symbol('b', integer=True)

        total_size = sum(sizes)
        total_size = substitute_by_name(total_size, {'a' : a, 'b': b})
        n = substitute_by_name(n, {'a' : a, 'b': b})
        total_size = simplify_floor_by_degree(total_size, a)
        total_size = simplify_floor_by_degree(total_size, b)
        
        matches = sp.expand(total_size - n) == 0
        if not matches:
            print(f"Total symbolic size = {total_size}, expected = {n}")
            for name in self.intervals:
                expr = self.intervals[name].symbolic_size()
                expr = expr.replace(sp.floor, lambda x: sp.simplify(x))
                expr = sp.simplify(expr, rational=True)
                print(f"{name} size = {expr}")

        return matches and disjoint
