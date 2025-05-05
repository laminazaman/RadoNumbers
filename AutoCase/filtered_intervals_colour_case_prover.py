import sympy as sp
from itertools import product
from filtered_interval import FilteredInterval
from z3_solver import Z3Solver
from z3_utils import IntegralityLemmaChecker_a_a_ap1
from z3_utils import IntegralityLemmaChecker_a_b_b
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
        self.contradiction_lemmas = []
        self.theorem = ""
        self.lemma_outcomes = {}
    
    def precompute_contradiction_lemmas(self):
        if self.theorem == "a.a.ap1":
            for i in range(len(self.contradiction_lemmas)):
                thm = self.contradiction_lemmas[i]
                result, duration, model, constraints = self.run_z3_proof_a_a_ap1(thm)
                self.lemma_outcomes[tuple(thm)] = {
                    'result': result,
                    'duration': duration,
                    'model': model,
                    'constraints': constraints
                }
        elif self.theorem == "a.b.b":
            for i in range(len(self.contradiction_lemmas)):
                thm = self.contradiction_lemmas[i]
                result, duration, model, constraints = self.run_z3_proof_a_b_b(thm)
                self.lemma_outcomes[tuple(thm)] = {
                    'result': result,
                    'duration': duration,
                    'model': model,
                    'constraints': constraints
                }


    def get(self):
        return {
            'statement': self.statement,
            'intervals': {interval: self.intervals[interval].get() for interval in self.intervals},
            'colouring': self.colouring,
            'equation': self.equation,
            'assumptions': self.assumptions
        }

    def add_contradiction_lemma(self, lem, thm):
        self.contradiction_lemmas.append(lem)
        self.theorem = thm

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
            #z_intervals = [name for name in self.colouring[col] if name >= earliest_interval]
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

    def get_z_expr(self, var_names=None):
        import sympy as sp
        n = len(self.equation)
        if var_names is None:
            var_names = [f'x{i+1}' for i in range(n)]
        vars = sp.symbols(var_names)

        lhs = sum(self.equation[i] * vars[i] for i in range(n - 1))
        z = vars[-1]
        return sp.solve(lhs - self.equation[-1] * z, z)[0]

    ########################################################################
    def find_interval_for_var(self, var, lhs_intervals, rhs_interval):
        var_str = str(var)
        if var_str.startswith("x_"):
            index = int(var_str.split("_")[1]) - 1
            if index < len(lhs_intervals):
                return self.intervals[lhs_intervals[index]]
            elif index == len(lhs_intervals):
                return self.intervals[rhs_interval]
        return None

    def run_z3_proof_a_a_ap1(self, thm):
        a = z3.Int("a")
        x1, x2, x3 = z3.Ints("x_1 x_2 x_3")

        equation = a * x1 + a * x2 == (a + 1) * x3
        assumptions = [a >= 7, a % 2 != 0]
        upper_bound_expr = 'a**3 * (a + 1)'
        div_tags = [(c[0], str(c[1]), str(c[2])) for c in thm]

        checker = IntegralityLemmaChecker_a_a_ap1(equation, assumptions, upper_bound_expr)

        if tuple(div_tags) == tuple([('divides', 'a**2', 'x_1'), ('divides', 'a**2', 'x_2'), ('divides', 'a**2', 'x_3')]):
            res, duration, reason, z3_cons = checker.prove_no_solution_Rr_case()
        else:
            res, duration, reason, z3_cons = checker.prove_no_integer_solution(div_tags)
        return (True, duration, thm, z3_cons) if res == z3.unsat else (False, duration, reason, z3_cons)

    def run_z3_proof_a_b_b(self, thm):
        a = z3.Int("a")
        b = z3.Int("b")
        x1, x2, x3 = z3.Ints("x_1 x_2 x_3")
       
        equation = a * x1 + b * x2 == b * x3
        assumptions = [a >= 4, b >= 3, a > b, a**2 + a + b > b**2 + a * b, a % 2 != 0]
        upper_bound_expr = 'a**3 + a**2 + (2*b + 1) * a'
        div_tags = [(c[0], str(c[1]), str(c[2])) for c in thm]

        checker = IntegralityLemmaChecker_a_b_b(equation, assumptions, upper_bound_expr)

        res, duration, reason, z3_cons = checker.prove_no_integer_solution(div_tags)
        return (True, duration, thm, z3_cons) if res == z3.unsat else (False, duration, reason, z3_cons)


    def contradiction_by_lemma(self, lhs_intervals, rhs_interval):
        result = False
        eq = self.equation
        if len(eq) != 3: return False, None, None

        if self.theorem not in ['a.a.ap1', 'a.b.b']: return False, None, None

        for i in range(len(self.contradiction_lemmas)):
            thm = self.contradiction_lemmas[i]
            
            result = True  
            for condition in thm:
                cond, d, var = condition[0], condition[1], str(condition[2])
                interval = self.find_interval_for_var(var, lhs_intervals, rhs_interval)
                if cond == 'divides':
                    result = result and (d in interval.must_divide)
                elif cond == 'not_divides':
                    result = result and (d in interval.must_not_divide)
            if result == True:
                if tuple(thm) in self.lemma_outcomes:
                    x = self.lemma_outcomes[tuple(thm)]
                    return x['result'], x['model'], x['constraints']                     
        return result, None, None
    ########################################################################
    def generate_proof(self, colour_cases):
        start = time.time()
        current_time = time.time()
        counts = {'SAT': 0, 'UNSAT': 0, 'UNKNOWN': 0}

        self.precompute_contradiction_lemmas()
        

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
                    res, reason, z3_cons = self.contradiction_by_lemma(lhs_intervals, target)
                    
                    if res == True:
                        print('INPUT CONSTRAINTS in Z3:')
                        print("----------------------------------------------------------------------------")
                        pprint.pprint(z3_cons)
                        print()

                        print(f"Contradiction by Lemma: {reason} ⇒ No integer solution")
                        counts['UNSAT'] += 1
                    
                        print(f"Case time: {time.time()-current_time:0.2f}; Elapsed time: {time.time()-start:0.2f}; Current counts: {counts}")
                        current_time = time.time()
                        print("############################################################################")
                        continue
                    else:
                                                
                        pass
                    eq_expr = sum(self.equation[i] * lhs_vars[i] for i in range(len(lhs_vars))) - self.equation[-1] * rhs_var
                    eq = sp.Eq(eq_expr, 0)
                    assumptions = self.assumptions
                    constraints = self.get_all_constraints(lhs_vars, lhs_intervals, rhs_var, target)
                    vars = Z3Solver.extract_all_symbols(constraints)
                    z3solver = Z3Solver(vars, constraints=[eq] + assumptions + constraints)
                    print('INPUT CONSTRAINTS in Z3:')
                    print("----------------------------------------------------------------------------")
                    pprint.pprint(z3solver.constraints)
                    print()
                    
                    result = z3solver.check()
                    if result == z3.unsat:
                        counts['UNSAT'] += 1
                        print(f"Z3 OUTPUT: UNSAT ⇒ {rhs_var} ∉ {target}")
                    elif result == z3.sat:
                        counts['SAT'] += 1
                        output_verified = False
                        pprint.pprint(z3solver.model(result))
                    else: counts['UNKNOWN'] += 1
                    
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

    def symbolic_difference_less_than_one(self, expr1, expr2, variables):
        from z3_solver import Z3Solver
        diff = sp.simplify(expr1 - expr2)
        constraint = sp.StrictLessThan(diff, 1)
        solver = Z3Solver(vars=variables, constraints=[constraint])
        check = solver.check()
        return check, solver.model(check)

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
            expr = sp.simplify(self.intervals[name].symbolic_size())
            expr = expr.replace(sp.floor, lambda x: sp.simplify(x))
            expr = sp.simplify(expr, rational=True)
            expr = sp.together(expr)

            sizes.append(expr)
        total_size = sp.simplify(sum(sizes))
        a = sp.Symbol('a', integer=True)
        check, model = self.symbolic_difference_less_than_one(total_size, n, list(n.free_symbols))
        matches = check 
        if not matches:
            print(f"Total symbolic size = {total_size}, expected = {n}")
            for name in self.intervals:
                expr = self.intervals[name].symbolic_size()
                expr = expr.replace(sp.floor, lambda x: sp.simplify(x))
                expr = sp.simplify(expr, rational=True)
                print(f"{name} size = {expr}")

        return matches and disjoint
