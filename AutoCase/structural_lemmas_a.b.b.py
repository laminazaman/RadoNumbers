import z3
import time
from z3_utils import IntegralityLemmaChecker_a_b_b


equation = z3.Int('a') * z3.Int('x_1') + z3.Int('b') * z3.Int('x_2') == z3.Int('b') * z3.Int('x_3')
assumptions = [
    z3.Int('a') >= 4,
    z3.Int('b') >= 3,
    z3.Int('a') > z3.Int('b'),
    z3.Int('a') * z3.Int('a') + z3.Int('a') + z3.Int('b') > z3.Int('b') * z3.Int('b') + z3.Int('a') * z3.Int('b')
]

upper_bound_expr = 'a**3 + a**2 + (2*b + 1) * a'
checker = IntegralityLemmaChecker_a_b_b(equation, assumptions, upper_bound_expr)

div_tags = [('divides', 'b**2', 'x_1'), ('not_divides', 'b', 'x_2'), ('not_divides', 'b', 'x_3')]
res, duration, model, constraints = checker.prove_no_integer_solution(div_tags)
print(f"Result: {res}, Duration: {duration:.2f}s")
if model: print("Counterexample:", model)


div_tags = [('divides', 'b**2', 'x_1'), ('divides', 'b**2', 'x_2'), ('divides', 'b**2', 'x_3')]
res, duration, model, constraints = checker.prove_no_integer_solution(div_tags)
print(f"Result: {res}, Duration: {duration:.2f}s")
if model: print("Counterexample:", model)

