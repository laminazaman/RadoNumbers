import sympy as sp

import pprint
from divitems import DivItems
from interval import Interval
from colour_case_prover import ColorCaseProver

# Define variables
a = sp.symbols('a', integer=True, positive=True)

# Define P_0, P_1, ..., P_6 as Sympy intervals
P0 = sp.Interval(1, a)
P1 = sp.Interval(a+1, a**2 + 2*a)
P2 = sp.Interval(a**2 + 2*a + 1, a**2 + 3*a)
P3 = sp.Interval(a**2 + 3*a + 1, a**3 + 4*a**2 + 4*a)
P4 = sp.Interval(a**3 + 4*a**2 + 4*a + 1, a**3 + 4*a**2 + 5*a)
P5 = sp.Interval(a**3 + 4*a**2 + 5*a + 1, a**3 + 5*a**2 + 6*a)
P6 = sp.Interval(a**3 + 5*a**2 + 6*a + 1, a**3 + 5*a**2 + 7*a)

substitution = {a: 1}

n = a**3 + 5*a**2 + 7*a

# Define the filtered sets as custom-defined intervals
D1 = Interval([a], P0, DivItems([]), substitution)
D2 = Interval([a], P2, DivItems([]), substitution)
D3 = Interval([a], P4, DivItems([]), substitution)
D4 = Interval([a], P6, DivItems([]), substitution)

R1 = Interval([a], P1, DivItems([]), substitution)
R2 = Interval([a], P5, DivItems([]), substitution)

B1 = Interval([a], P3, DivItems([]), substitution)


ccp = ColorCaseProver()

ccp.set_equation([a, 1, 1])
ccp.set_substitution(substitution)
ccp.set_statement("Example: For a >= 1, R_3(E(3, 0; a, 1, 1)) >= a^3+5a^2+7a+1.")

ccp.add_interval("D1", D1)
ccp.add_interval("D2", D2)
ccp.add_interval("D3", D3)
ccp.add_interval("D4", D4)
ccp.add_interval("R1", R1)
ccp.add_interval("R2", R2)
ccp.add_interval("B1", B1)

ccp.add_intervals_to_colour(0, ["D1", "D2", "D3", "D4"])
ccp.add_intervals_to_colour(1, ["R1", "R2"])
ccp.add_intervals_to_colour(2, ["B1"])

cases = ccp.generate_cases(n)
ccp.generate_proof(cases)
