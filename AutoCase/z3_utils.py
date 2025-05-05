import z3
import time

class IntegralityLemmaChecker_a_b_b:
    def __init__(self, equation, assumptions, upper_bound_expr):
        self.equation = equation
        self.assumptions = assumptions
        self.upper_bound_expr = upper_bound_expr
        self.z3_vars = {
            'x_1': z3.Int('x_1'),
            'x_2': z3.Int('x_2'),
            'x_3': z3.Int('x_3'),
            'a': z3.Int('a'),
            'b': z3.Int('b')
        }

    def parse_expr(self, expr_string):
        if isinstance(expr_string, str):
            return eval(expr_string, {}, self.z3_vars)
        elif isinstance(expr_string, z3.ExprRef):
            return expr_string
        elif isinstance(expr_string, int):
            return z3.IntVal(expr_string)
        raise ValueError(f"Unsupported expression: {expr_string}")

    def gcd_is_one(self, a, b):
        d = z3.Int('d')
        return z3.ForAll(d, z3.Implies(z3.And(d > 1, a % d == 0, b % d == 0), False))

    def safe_div_constraint(self, tag, d_expr, x_str):
        x = self.z3_vars[x_str]
        d = self.parse_expr(d_expr)
        k = z3.Int(f'k_{x_str}')
        if tag == 'divides':
            return [x == d * k, k > 0], [k]
        elif tag == 'not_divides':
            return [x != d * k], [k]
        else:
            raise ValueError(f"Unsupported tag: {tag}")

    def prove_no_integer_solution(self, div_tags):
        N = self.parse_expr(self.upper_bound_expr)
        constraints = []

        quantified_vars = list(self.z3_vars.values())
        x_vars = ['x_1', 'x_2', 'x_3']
        for var_name in x_vars:
            x = self.z3_vars[var_name]
            constraints.append(z3.And(x >= 1, x <= N))

        for tag, d_expr, x_str in div_tags:
            div_cons, k_vars = self.safe_div_constraint(tag, d_expr, x_str)
            constraints.extend(div_cons)
            quantified_vars.extend(k_vars)

        quantified_vars = list(set(quantified_vars))

        # Add gcd(a, b) = 1 if not explicitly included
        a = self.z3_vars['a']
        b = self.z3_vars['b']
        if all("GCD" not in str(asm) for asm in self.assumptions):
            self.assumptions.append(self.gcd_is_one(a, b))

        solver = z3.Solver()
        solver.set("timeout", 300000)
        formula = z3.ForAll(
            quantified_vars,
            z3.Implies(
                z3.And(*self.assumptions),
                z3.Not(z3.And(*(constraints + [self.equation])))
            )
        )
        solver.add(formula)

        start = time.time()
        result = solver.check()
        duration = time.time() - start
        model = solver.model() if result == z3.sat else None
        all_constraints = [self.equation] + self.assumptions + constraints
        return result, duration, model, all_constraints


class IntegralityLemmaChecker_a_a_ap1:
    def __init__(self, equation, assumptions, upper_bound_expr):
        self.equation = equation
        self.assumptions = assumptions
        self.upper_bound_expr = upper_bound_expr
        self.z3_vars = {
            'x_1': z3.Int('x_1'),
            'x_2': z3.Int('x_2'),
            'x_3': z3.Int('x_3'),
            'a': z3.Int('a')
        }

    def parse_expr(self, expr_string):
        if isinstance(expr_string, str):
            return eval(expr_string, {}, self.z3_vars)
        elif isinstance(expr_string, z3.ExprRef):
            return expr_string
        elif isinstance(expr_string, int):
            return z3.IntVal(expr_string)
        raise ValueError(f"Unsupported expression: {expr_string}")

    def safe_div_constraint(self, tag, d_expr, x_str):
        x = self.z3_vars[x_str]
        d = self.parse_expr(d_expr)
        k = z3.Int(f'k_{x_str}')
        if tag == 'divides':
            return [x == d * k, k > 0], [k]
        elif tag == 'not_divides':
            return [x != d * k], [k]
        else:
            raise ValueError(f"Unsupported tag: {tag}")

    def prove_no_integer_solution(self, div_tags):
        N = self.parse_expr(self.upper_bound_expr)
        constraints = []

        quantified_vars = list(self.z3_vars.values())

        for var_name in ['x_1', 'x_2', 'x_3']:
            x = self.z3_vars[var_name]
            constraints.append(z3.And(x >= 1, x <= N))

        for tag, d_expr, x_str in div_tags:
            div_cons, k_vars = self.safe_div_constraint(tag, d_expr, x_str)
            constraints.extend(div_cons)
            quantified_vars.extend(k_vars)

        quantified_vars = list(set(quantified_vars))  # Deduplicate

        solver = z3.Solver()
        solver.set("timeout", 300000)
        formula = z3.ForAll(
            quantified_vars,
            z3.Implies(
                z3.And(*self.assumptions),
                z3.Not(z3.And(*(constraints + [self.equation])))
            )
        )
        solver.add(formula)
        start = time.time()
        result = solver.check()
        duration = time.time() - start
        model = solver.model() if result == z3.sat else None
        all_constraints = [self.equation] + self.assumptions + constraints
        return result, duration, model, all_constraints

    def prove_no_solution_Rr_case(self):
        a, k1, k2, k3 = z3.Ints('a k1 k2 k3')

        # From R_r structure: x_i = a^2 * k_i
        equation = a * (k1 + k2) == (a + 1) * k3
        assumptions = [
            a >= 7,
            a % 2 != 0,
            k1 >= 1, k1 < a,
            k2 >= 1, k2 < a,
            k3 >= 1, k3 < a,
            (k1 + k2) % (a + 1) == 0
        ]

        solver = z3.Solver()
        solver.set("timeout", 300000)
        solver.add(assumptions)
        solver.add(equation)

        start = time.time()
        result = solver.check()
        duration = time.time() - start
        model = solver.model() if result == z3.sat else None

        return result, duration, model, assumptions + [equation]