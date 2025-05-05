import z3
import sympy as sp

class Z3Solver:
    def __init__(self, vars = [], constraints = []):
        constraints = self.rewrite_divisibles(constraints)
        self.vars = self.to_z3_vars(vars)  # {'a': Int('a'), 'b': Int('b'), ...}
        self.constraints = self.to_z3_constraints(constraints)
        self.solver = z3.Solver()
        self.solver.add(*self.constraints)

    def to_z3_vars(self, vars):
        z3_vars = {}
        for v in vars:
            z3_vars[str(v)] = z3.Int(str(v))
        return z3_vars
    ################################################################
    @staticmethod
    def extract_all_symbols(constraints):
        from sympy import preorder_traversal, Symbol
        symbols = set()
        for c in constraints:
            if isinstance(c, tuple):
                args = c[1:]  # skip the tag
            else:
                args = [c]
            for expr in args:
                if hasattr(expr, 'free_symbols'):
                    symbols |= expr.free_symbols
                elif isinstance(expr, Symbol):
                    symbols.add(expr)
        return list(symbols)


    @staticmethod
    def is_prime_z3(n):
        k = z3.Int("k")
        q = z3.Int("q")

        not_divisible = z3.Not(z3.Exists([k, q], z3.And(
            k > 1,
            k < n,
            q > 0,
            n == k * q
        )))
        return z3.And(n > 1, not_divisible)

    def gcd_multi_z3(self, args):
        g = z3.Int(f"gcd_{'_'.join(str(arg) for arg in args)}")
        t = z3.Int("t_gcd_check")

        divisibility = z3.And(*[(arg % g == 0) for arg in args])
        maximality = z3.ForAll(t, z3.Implies(
            z3.And(t > 0, *[(arg % t == 0) for arg in args]),
            t <= g
        ))

        return z3.Exists(g, z3.And(g > 0, divisibility, maximality))

    def lcm_multi_z3(self, args):
        x = z3.Int(f"lcm_{'_'.join(str(arg) for arg in args)}")
        t = z3.Int("t_lcm_test")

        divisible_by_all = z3.And(*[(x % arg == 0) for arg in args])
        minimality = z3.ForAll(t, z3.Implies(
            z3.And(t > 0, *[(t % arg == 0) for arg in args]),
            x <= t
        ))

        return z3.Exists(x, z3.And(x > 0, divisible_by_all, minimality))

    def cross_multiply_constraint(self, expr):
        if isinstance(expr, sp.Rel):
            lhs = sp.together(expr.lhs)
            rhs = sp.together(expr.rhs)

            lhs_num, lhs_den = sp.fraction(lhs)
            rhs_num, rhs_den = sp.fraction(rhs)

            lhs_expr = lhs_num * rhs_den
            rhs_expr = rhs_num * lhs_den
            return expr.func(lhs_expr, rhs_expr)
        
        return expr

    def divisible_by(self, x, d):
        z3_k = z3.Int("k")
        return z3.Exists([z3_k], z3.And(z3_k > 0, x == d * z3_k))

    def not_divisible_by(self, x, d):
        z3_k = z3.Int("k")
        return z3.ForAll([z3_k], z3.And(z3_k > 0, x != d * z3_k))
    ################################################################

    def sp_to_z3_expr(self, expr, z3_vars):
        if isinstance(expr, sp.core.relational.Relational):
            lhs = self.sp_to_z3_expr(expr.lhs, z3_vars)
            rhs = self.sp_to_z3_expr(expr.rhs, z3_vars)
            op = expr.rel_op
            if op == '==': return lhs == rhs
            elif op == '!=': return lhs != rhs
            elif op == '>': return lhs > rhs
            elif op == '>=': return lhs >= rhs
            elif op == '<': return lhs < rhs
            elif op == '<=': return lhs <= rhs
            else: 
                raise NotImplementedError(f"Unknown rel_op: {op}")
        elif isinstance(expr, (int, sp.Integer)): return z3.IntVal(int(expr))
        elif isinstance(expr, (float, sp.Float)): return z3.RealVal(float(expr))
        elif isinstance(expr, (bool)): return z3.BoolVal(bool(expr))
        elif expr in (sp.true, sp.false): return z3.BoolVal(bool(expr))
        elif isinstance(expr, sp.Add): return sum(self.sp_to_z3_expr(arg, z3_vars) for arg in expr.args) 
        elif isinstance(expr, sp.And): return z3.And(*[self.sp_to_z3_expr(arg, z3_vars) for arg in expr.args])
        elif isinstance(expr, sp.Or): return z3.Or(*[self.sp_to_z3_expr(arg, z3_vars) for arg in expr.args])
        elif isinstance(expr, sp.Not): return z3.Not(self.sp_to_z3_expr(expr.args[0], z3_vars))
        elif isinstance(expr, sp.Mul):
            result = self.sp_to_z3_expr(expr.args[0], z3_vars)
            for arg in expr.args[1:]:
                result *= self.sp_to_z3_expr(arg, z3_vars)
            return result
        elif isinstance(expr, sp.Pow):
            base, exp = expr.args
            base_z3 = self.sp_to_z3_expr(base, z3_vars)
            exp_z3 = self.sp_to_z3_expr(exp, z3_vars)
            if not (z3.is_expr(base_z3) and z3.is_expr(exp_z3)):
                raise ValueError(f"Invalid power base or exponent: {base_z3}, {exp_z3}")
            pow_expr = base_z3 ** exp_z3 # z3.ToInt(base_z3 ** exp_z3)    
            return pow_expr

        elif hasattr(expr, "func") and expr.func.__name__ == 'Mod':
            a, b = expr.args
            a_z3 = self.sp_to_z3_expr(a, z3_vars)
            b_z3 = self.sp_to_z3_expr(b, z3_vars)
            
            if not (z3.is_expr(a_z3) and a_z3.sort_kind() == z3.Z3_INT_SORT):
                raise ValueError(f"Z3 Mod: first argument not Int: {a} → {a_z3}")
            if not (z3.is_expr(b_z3) and b_z3.sort_kind() == z3.Z3_INT_SORT):
                raise ValueError(f"Z3 Mod: second argument not Int: {b} → {b_z3}")
            return a_z3 % b_z3
        elif hasattr(expr, "func") and expr.func.__name__ == 'gcd':
            args = expr.args
            if len(args) != 2:
                raise NotImplementedError("Only gcd(a, b) for 2 arguments is supported.")
            a_z3 = self.sp_to_z3_expr(args[0], z3_vars)
            b_z3 = self.sp_to_z3_expr(args[1], z3_vars)

            t = z3.Int("t_gcd_check")
            # For all t in Z: (t>1) => ('t does not divide a' or 't does not divide b')
            #no_common_divisor = z3.ForAll(t, z3.Or(t <= 1, z3.Or(a_z3 % t != 0, b_z3 % t != 0)))
            no_common_divisor = z3.ForAll(t, z3.Or(t <= 1, a_z3 % t != 0, b_z3 % t != 0))
            return no_common_divisor
                
        elif isinstance(expr, sp.Symbol):
            name = str(expr)
            return z3_vars.get(name, z3.Int(name))
        else:
            raise ValueError(f"[sp_to_z3_expr] Unsupported expression: {repr(expr)} (type: {type(expr)})")

    def flatten_constraints(self, constraint):
        # If it's a conjunction, split it
        if isinstance(constraint, sp.And):
            return list(constraint.args)
        return [constraint]

    def to_z3_constraints(self, constraints):
        z3_constraints = []
        for c in constraints:
            if c in [True, False]:
                if c: continue  # True adds nothing
                else: z3_constraints.append(False)  # Unsatisfiable
                continue
            elif isinstance(c, sp.floor):
                arg = self.sp_to_z3_expr(c.args[0], self.vars)
                return z3.ToInt(arg)
            elif isinstance(c, tuple):
                tag = c[0]
                args = c[1:]

                if tag == 'odd':
                    var = args[0]
                    z3_var = self.vars[str(var)]
                    z3_constraints.append(z3_var % 2 == 1)
                    continue

                elif tag == 'even':
                    var = args[0]
                    z3_var = self.vars[str(var)]
                    z3_constraints.append(z3_var % 2 == 0)
                    continue                
                elif tag == 'divides':
                    d, n, ub = args[0], args[1], args[2]
                    d_z3 = self.sp_to_z3_expr(d, self.vars)
                    n_z3 = self.sp_to_z3_expr(n, self.vars)
                    z3_constraints.append(self.divisible_by(n_z3, d_z3))
                    continue            
                elif tag == 'not_divides':
                    d, n = args[0], args[1]
                    d_z3 = self.sp_to_z3_expr(d, self.vars)
                    n_z3 = self.sp_to_z3_expr(n, self.vars)
                    z3_constraints.append(self.not_divisible_by(n_z3, d_z3))
                    continue

            try:
                for sub_c in self.flatten_constraints(c):
                    if isinstance(sub_c, (sp.Rel, sp.Expr)):
                        sub_c = sp.expand(self.cross_multiply_constraint(sub_c))

                    z3_c = self.sp_to_z3_expr(sub_c, self.vars) 
                    if z3_c is None: raise ValueError(f"Expression converted to None: {sub_c}")
                    z3_constraints.append(z3_c)
            except Exception as e:
                raise ValueError(f"Failed to convert constraint: {c}\nError: {e}")

        return z3_constraints            
    ################################################################

    def rewrite_divisibles(self, constraints):
        replacements = {}   # maps x -> (d, k_x)
        new_constraints = []

        # First pass: identify and record substitutions
        for c in constraints:
            if isinstance(c, tuple) and c[0] == 'divides':
                d, x = c[1], c[2]
                k = sp.Symbol(f'k_{x}', integer=True)
                replacements[x] = (d, k)
            else:
                new_constraints.append(c)

        # Second pass: apply substitutions
        substituted_constraints = []
        for expr in new_constraints:
            if isinstance(expr, (sp.Rel, sp.Expr)):
                substituted = expr
                for x, (d, k) in replacements.items():
                    substituted = substituted.subs(x, d * k)
                substituted_constraints.append(substituted)
            else:
                substituted_constraints.append(expr)
        
        # Add replacement equations and bounds: x = d * k, k ≥ 1
        for x, (d, k) in replacements.items():
            substituted_constraints.append(sp.Ge(k, 1))
            substituted_constraints.append(sp.Eq(x, d * k))  # optional, for traceability

        return substituted_constraints

    def rewrite_must_not_divide(self, constraints):
        """
        Replaces each ('must_not_divide', d, x, ub) with constraints:
        - x ≠ k * d  for all k in [1, floor(ub / d)]
        Assumes all arguments are SymPy expressions.
        """
        print(constraints)
        new_constraints = []

        for c in constraints:
            if isinstance(c, tuple) and c[0] == 'not_divides':
                d, x, ub = c[1], c[2], c[3]

                # Estimate how many values to exclude
                try:
                    # If ub and d are concrete, determine the max k directly
                    max_k = int(sp.floor(ub / d)
                    )
                except TypeError:
                    # If symbolic, pick a conservative symbolic k range
                    k = sp.Symbol(f"k_excl_{x}", integer=True)
                    mod_expr = sp.Ne(sp.Mod(x, d), 0)
                    new_constraints.append(mod_expr)
                    continue

                # Add exclusion constraints: x ≠ d·k for k = 1 to max_k
                exclusions = [sp.Ne(x, d * k) for k in range(1, max_k + 1)]
                new_constraints.append(sp.And(*exclusions))
            else:
                new_constraints.append(c)

        return new_constraints

    def check(self):
        if True in self.constraints or False in self.constraints:
            return "Error"
        check = self.solver.check() 
        return check

    def model(self, check):
        if check == z3.sat:
            return self.solver.model()
        return None
