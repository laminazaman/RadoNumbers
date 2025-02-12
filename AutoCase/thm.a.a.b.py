import sympy as sp

import pprint
from divitems import DivItems
from interval import Interval
from divisibility import Divisibility
from colour_case_prover import ColorCaseProver

# Define variables
a = sp.symbols('a', integer=True, positive=True)

substitution = {a : 7}

# Define as a Sympy interval
A0 = sp.Interval(1, a**3 * (a + 1)-1)
S0 = sp.Interval(a**4 + a**2, a**4 + a**3 - a**2)
S1 = sp.Interval(a**3, a**2 * (a**2 - 3) / 2)
S2 = sp.Interval(a**3 * (a+1) / 2 + a**2, a**4 - a**2)
PL = sp.Interval(1, a**3 * (a + 1)-1)

# Define the filtered sets as custom-defined intervals

# Define filtered intervals for {A}_0(a)
D_1 = Interval([a], A0, DivItems([(a, True), (a**2, False)]), substitution)

# Define filtered intervals for {A^r}_2(a)
B_1 = Interval([a], S0, DivItems([(a**2, True)]), substitution)
B_2 = Interval([a], S1, DivItems([(a**2, True), (a**3, True)]), substitution)
B_3 = Interval([a], S2, DivItems([(a**2, True), (a**3, False)]), substitution)

# Define filtered intervals for {A^l}_2(a)
PL2 = Interval([a], PL, DivItems([(a, False)]), substitution)


ccp = ColorCaseProver()
ccp.set_statement("Theorem for E(3, 0; a, a, a+ 1).")

ccp.add_interval("D_1", D_1)

ccp.add_interval("B_1", B_1)
ccp.add_interval("B_2", B_2)
ccp.add_interval("B_3", B_3)
ccp.add_interval("PL2", PL2)

ccp.set_equation([1, 1, (1+1/a)])
ccp.set_substitution(substitution)

ccp.add_intervals_to_colour(0, ["D_1"])
ccp.add_intervals_to_colour(2, ["B_1"])
ccp.add_intervals_to_colour(2, ["B_2"])
ccp.add_intervals_to_colour(2, ["B_3"])
ccp.add_intervals_to_colour(2, ["PL2"])

cases = ccp.generate_cases()

ccp.generate_proof(cases)
