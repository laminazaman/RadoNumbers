import z3
import time

from z3_utils import IntegralityLemmaChecker_a_a_ap1

# Example Usage
equation = z3.Int('a') * z3.Int('x_1') + z3.Int('a') * z3.Int('x_2') == (z3.Int('a') + 1) * z3.Int('x_3')
assumptions = [z3.Int('a') >= 7, z3.Int('a') % 2 != 0]
upper_bound_expr = z3.Int('a')**3 * (z3.Int('a')+1) #'a**3 * (a + 1)'

cases = {
    'a': [('not_divides', 'a', 'x_1'), ('not_divides', 'a', 'x_2'), ('not_divides', 'a', 'x_3')],
    'b': [('divides', 'a', 'x_1'), ('divides', 'a', 'x_2'), ('divides', 'a', 'x_3'),
          ('not_divides', 'a**2', 'x_1'), ('not_divides', 'a**2', 'x_2'), ('not_divides', 'a**2', 'x_3')],
    'c': [('divides', 'a**2', 'x_1'), ('divides', 'a**2', 'x_2'), ('not_divides', 'a', 'x_3')],
    'd': [('divides', 'a**2', 'x_1'), ('not_divides', 'a', 'x_2'), ('divides', 'a**2', 'x_3')],
    'e': [('not_divides', 'a', 'x_1'), ('divides', 'a**2', 'x_2'), ('divides', 'a**2', 'x_3')],
    'f': [('divides', 'a**2', 'x_1'), ('not_divides', 'a', 'x_2'), ('not_divides', 'a', 'x_3')],
    'g': [('not_divides', 'a', 'x_1'), ('divides', 'a**2', 'x_2'), ('not_divides', 'a', 'x_3')]
}

checker = IntegralityLemmaChecker_a_a_ap1(equation, assumptions, upper_bound_expr)

for label, tags in cases.items():
    result, t, reason, constraints = checker.prove_no_integer_solution(tags)
    print(f'Case {label}: {constraints}', result, reason, f'{t:.3f}s')
