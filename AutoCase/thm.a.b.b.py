import sympy as sp
from filtered_interval import FilteredInterval
from filtered_intervals_colour_case_prover import FilteredIntervalsColorCaseProver
import pprint

# Define variables
a, b = sp.symbols('a b', integer=True)
x_1, x_2, x_3 = sp.symbols('x_1 x_2 x_3', integer=True)

GCD = sp.Function("gcd")
# Define assumptions
assumptions = [
    a >= 4, b >= 3, a > b, a**2 + a + b > b**2 + a * b, 
    sp.Eq(GCD(a, b), 1, evaluate=False)
    ]

# Define total endpoint
n = a**3 + a**2 + (2 * b + 1) * a

# Define prover
prover = FilteredIntervalsColorCaseProver()
prover.set_equation([a, b, b])
prover.set_assumptions(assumptions)
prover.set_statement(
    "Theorem: Given positive integers $a$ and $b$ with $a^2+a+b > b^2+ab$ and $a\\geq b\\geq 3$, if $\\gcd(a, b)=1$, "
    "then \\[{{R_3}}({{\\cal E}}(3, 0; a, b, b)) \\geq a^3 + a^2 + (2b+1)a + 1.\\]"
)

# Define filtered intervals
R1 = FilteredInterval([a, b], assumptions)
R1.set_bounds(1, a * b)
R1.add_must_not_divide(b)
prover.add_interval("R1", R1)

R2 = FilteredInterval([a, b], assumptions)
R2.set_bounds(b**2, b**2 * a)
R2.add_must_divide(b**2)
prover.add_interval("R2", R2)

R3 = FilteredInterval([a, b], assumptions)
R3.set_bounds(a**3 + a**2 + (b + 1) * a + 1, n)
prover.add_interval("R3", R3)

B1 = FilteredInterval([a, b], assumptions)
B1.set_bounds(1, b**2 * a)
B1.add_must_divide(b)
B1.add_must_not_divide(b**2)
prover.add_interval("B1", B1)

B2 = FilteredInterval([a, b], assumptions)
B2.set_bounds(b**2 * a + 1, b * a**2 + b * a)
B2.add_must_divide(b)
prover.add_interval("B2", B2)

D1 = FilteredInterval([a, b], assumptions)
D1.set_bounds(b*a + 1, b * a**2 + b * a)
D1.add_must_not_divide(b)
prover.add_interval("D1", D1)

D2 = FilteredInterval([a, b], assumptions)
D2.set_bounds(b * a**2 + b * a + 1, a**3 + a**2 + (b + 1) * a)
prover.add_interval("D2", D2)

# Assign colours
prover.add_intervals_to_colour(0, ["D1", "D2"])
prover.add_intervals_to_colour(1, ["R1", "R2", "R3"])
prover.add_intervals_to_colour(2, ["B1", "B2"])

# Add contradiction theorems
prover.add_contradiction_lemma([('divides', b**2, x_1), ('not_divides', b, x_2), ('not_divides', b, x_3)], "a.b.b")

# ax_1+bx_2=bx_3 with 1 <= x_1,x_2,x_3 <= ab^2; implies ak_1+bk_2=bk_3 with 1 <= k_1, k_2, k_3 <=a
# k_1 = (b/a)(k_3 - k_2).. no integer solution
prover.add_contradiction_lemma([('divides', b**2, x_1), ('divides', b**2, x_2), ('divides', b**2, x_3)], "a.b.b")

# Generate cases and proof
print("Prover setup:")
print("----------------------------------------------------------------------------")
pprint.pprint(prover.get())
print("----------------------------------------------------------------------------")
print()

print("Partition check:")
print("----------------------------------------------------------------------------")
prover.check_partition(n)
print("----------------------------------------------------------------------------")
print()

colour_cases = prover.generate_cases(n)
print("Colour cases:")
print("----------------------------------------------------------------------------")
pprint.pprint(colour_cases)
print("----------------------------------------------------------------------------")
print()

prover.generate_proof(colour_cases)
