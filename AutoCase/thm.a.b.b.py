import sympy as sp

import pprint
from divitems import DivItems
from interval import Interval
from colour_case_prover import ColorCaseProver

# Define variables
a, b = sp.symbols('a b', integer=True, positive=True)

# Define P_0, P_1, ..., P_4 as Sympy intervals
P0 = sp.Interval(1, a * b)
P1 = sp.Interval(b*a + 1, b**2 * a)
P2 = sp.Interval(b**2 * a + 1, b * a**2 + b * a)
P3 = sp.Interval(b * a**2 + b * a + 1, a**3 + a**2 + (b + 1) * a)
P4 = sp.Interval(a**3 + a**2 + (b + 1) * a + 1, a**3 + a**2 + (2 * b + 1) * a)

P0UP1 = sp.Interval(1, b**2 * a)
P1UP2 = sp.Interval(b*a + 1, b * a**2 + b * a)

substitution = {a: 4, b: 3}

# Define the filtered sets as custom-defined intervals
R1 = Interval([a,b], P0, DivItems([(b, False)]), substitution)
R2 = Interval([a,b], P0UP1, DivItems([(b**2, True)]), substitution)
R3 = Interval([a,b], P4, DivItems([]), substitution)

B1 = Interval([a,b], P0UP1, DivItems([(b, True), (b**2, False)]), substitution)
B2 = Interval([a,b], P2, DivItems([(b, True)]), substitution)

D1 = Interval([a,b], P1UP2, DivItems([(b, False)]), substitution)
D2 = Interval([a,b], P3, DivItems([(b, True)]), substitution)

ccp = ColorCaseProver()

ccp.set_equation([a/b, 1, 1])
ccp.set_substitution(substitution)
ccp.set_statement("Theorem: Given positive integers $a$ and $b$ with $a^2+a+b > b^2+ba$ and $a\\geq b\\geq 3$, if $\\gcd(a, b)=1$, then \\[{R_3}({\\cal E}(3, 0; a, b, b)) \\geq a^3 + a^2 + (2b+1)a + 1.\\]")

ccp.add_interval("R1", R1)
ccp.add_interval("R2", R2)
ccp.add_interval("R3", R3)
ccp.add_interval("B1", B1)
ccp.add_interval("B2", B2)
ccp.add_interval("D1", D1)
ccp.add_interval("D2", D2)

ccp.add_intervals_to_colour(0, ["D1", "D2"])
ccp.add_intervals_to_colour(1, ["R1", "R2", "R3"])
ccp.add_intervals_to_colour(2, ["B1", "B2"])


cases = ccp.generate_cases()
ccp.generate_proof(cases)
