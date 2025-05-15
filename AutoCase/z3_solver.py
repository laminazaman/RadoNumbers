import z3
from z3 import *
import sympy as sp

class Z3Solver:
    def __init__(self, vars = [], constraints = [], div_tags = []):
        constraints = constraints 
        self.vars = self.to_z3_vars(vars)  # {'a': Int('a'), 'b': Int('b'), ...}
        self.constraints = self.to_z3_constraints(constraints) 
        self.solver = z3.Solver()
        self.solver.add(*self.constraints)
        self.solver.set("timeout", 10000) 
            
    def to_z3_vars(self, sympy_vars): return { str(v) : z3.Int(str(v)) for v in sympy_vars }

    @staticmethod
    def extract_z3_symbols(z3_constraints):
        if isinstance(z3_constraints, (BoolRef, ArithRef)): z3_constraints = [z3_constraints]
        vars_set = set().union(*[z3util.get_vars(c) for c in z3_constraints])
        return vars_set

    @staticmethod
    def extract_all_symbols(constraints):
        symbols = set()
        for c in constraints:
            exprs = c[1:] if isinstance(c, tuple) else [c]
            for expr in exprs:
                symbols |= expr.free_symbols if hasattr(expr, 'free_symbols') else {expr} if isinstance(expr, sp.Symbol) else set()
        return list(symbols)

    def divisible_by(self, x, d):
        k = z3.Int(f"k_{x}")
        return z3.And(k > 0, x == d * k)

    def not_divisible_by(self, x, d):
        k = z3.Int(f"k_{x}")
        return z3.ForAll([k], z3.And(k > 0, k<=x/d, x != d * k))

    def to_z3_constraints(self, constraints):
        z3_constraints = []

        for c in constraints:
            if c is True:
                continue  # no-op
            if c is False:
                z3_constraints.append(False)  # unsatisfiable
                continue

            if isinstance(c, sp.floor):
                arg = self.sp_to_z3_expr(c.args[0], self.vars)
                z3_constraints.append(z3.ToInt(arg))
                continue

            if isinstance(c, tuple):
                tag, *args = c

                if tag in ('odd', 'even'):
                    var = self.vars[str(args[0])]
                    z3_constraints.append(var % 2 == (1 if tag == 'odd' else 0))
                    continue

                if tag == 'divides':
                    d, x = self.sp_to_z3_expr(args[0], self.vars), self.sp_to_z3_expr(args[1], self.vars)
                    z3_constraints.append(self.divisible_by(x, d))
                    continue

                if tag == 'not_divides':
                    d, x = self.sp_to_z3_expr(args[0], self.vars), self.sp_to_z3_expr(args[1], self.vars)
                    z3_constraints.append(self.not_divisible_by(x, d))
                    continue

            try:
                for sub_c in self.flatten_constraints(c):
                    if isinstance(sub_c, (sp.Rel, sp.Expr)):
                        sub_c = sp.expand(self.cross_multiply_constraint(sub_c))
                        z3_c = self.sp_to_z3_expr(sub_c, self.vars)
                        if z3_c is None:
                            raise ValueError(f"Expression converted to None: {sub_c}")
                        z3_constraints.append(z3_c)
            except Exception as e:
                raise ValueError(f"Failed to convert constraint: {c}\nError: {e}")

        return z3_constraints


    ################################################################

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
            pow_expr = z3.ToInt(base_z3 ** exp_z3)    
            return pow_expr

        elif hasattr(expr, "func") and expr.func.__name__ == 'Mod':
            a, b = expr.args
            a_z3 = self.sp_to_z3_expr(a, z3_vars)
            b_z3 = self.sp_to_z3_expr(b, z3_vars)
            
            if not (z3.is_expr(a_z3) and a_z3.sort_kind() == z3.Z3_INT_SORT):
                raise ValueError(f"Z3 Mod: first argument not Int: {a} -> {a_z3}")
            if not (z3.is_expr(b_z3) and b_z3.sort_kind() == z3.Z3_INT_SORT):
                raise ValueError(f"Z3 Mod: second argument not Int: {b} -> {b_z3}")
            return a_z3 % b_z3
        elif hasattr(expr, "func") and expr.func.__name__ == 'coprime':
            args = expr.args
            if len(args) != 2:
                raise NotImplementedError("Only coprime(a, b) for 2 arguments is supported.")
            a_z3 = self.sp_to_z3_expr(args[0], z3_vars)
            b_z3 = self.sp_to_z3_expr(args[1], z3_vars)

            t = z3.Int("g")
            #is_coprime = z3.ForAll(t, z3.Or(t <= 1, a_z3 % t != 0, b_z3 % t != 0))
            is_coprime = z3.ForAll(t, z3.Implies(z3.And(t > 1, a_z3 % t == 0, b_z3 % t == 0), False))
            return is_coprime
                
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

    ################################################################
    def check(self):
        if True in self.constraints or False in self.constraints:
            return "Error"
        check = self.solver.check() 
        return check

    def model(self, check):
        if check == z3.sat:
            return self.solver.model()
        return None
