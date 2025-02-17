import sympy as sp

import pprint
from divitems import DivItems
from interval import Interval
from divisibility import Divisibility
from constraint import Constraint
from colour_case_prover import ColorCaseProver

# Define variables
a, i, j, k = sp.symbols('a i j k', integer=True, positive=True)

substitution = {a : 7}

# Define as a Sympy interval
A0 = sp.Interval(1, a**3 * (a + 1)-1)
S0 = sp.Interval(a**4 + a**2, a**4 + a**3 - a**2)
S1 = sp.Interval(a**3, a**2 * (a**2 - 3) / 2)
S2 = sp.Interval(a**3 * (a+1) / 2, a**4 - a**2)
PL = sp.Interval(1, a**3 * (a + 1)-1)

n = a**3 * (a + 1)-1
# Define the filtered sets as custom-defined intervals

# Define filtered intervals for {A}_0(a)
D_1 = Interval([a], A0, DivItems([(a, True), (a**2, False)]), substitution)

# Define filtered intervals for {A^r}_2(a)
C_B1 = Constraint({'a**4': [1, a**4], 'a**2': [i, a**2]}, {i:[1,a-1]}, True, substitution)
B_1 = Interval([a], S0, DivItems([(a**2, True)]), substitution, C_B1)

C_B2 = Constraint({'a**3': [i, a**3], 'a**2': [j, a**2]}, {i:[1,(a-1)/2], j:[0,i-1]}, True, substitution)
B_2 = Interval([a], S1, DivItems([(a**2, True)]), substitution, C_B2)

C_B3 = Constraint({'a**3': [i, a**3], 'a**2': [j, a**2]}, {i:[(a+1)/2, a-1], j:[0,i]}, True, substitution)
B_3 = Interval([a], S2, DivItems([(a**2, True)]), substitution, C_B3)

# Define filtered intervals for {A^r}_1(a)
C_R1 = Constraint({'a**4': [1, a**4], 'a**2': [i, a**2]}, {i:[1,a-1]}, False, substitution)
C_R2 = Constraint({'a**3': [i, a**3], 'a**2': [j, a**2]}, {i:[1,(a-1)/2], j:[0,i-1]}, False, substitution)
C_R3 = Constraint({'a**3': [i, a**3], 'a**2': [j, a**2]}, {i:[(a+1)/2, a-1], j:[0,i]}, False, substitution)

R_1 = Interval([a], A0, DivItems([(a**2, True)]), substitution, None, [C_R1, C_R2, C_R3])

# Define filtered intervals for {A^l}_2(a)
C_B4 = Constraint({'a*(a+1)': [i, a*(a+1)], 'a': [j, a], '1': [k, 1]}, {i: [0, a**2-1], j:[0, a], k:[1,2*sp.floor(j/2)]}, True, substitution)
B_4 = Interval([a], PL, DivItems([(a, False)]), substitution, C_B4)

# Define filtered intervals for {A^l}_1(a)
C_R4 = Constraint({'a*(a+1)': [i, a*(a+1)], 'a': [j, a], '1': [k, 1]}, {i: [0, a**2-1], j:[0, a], k:[2*sp.floor(j/2)+1, a-1]}, True, substitution)
R_2 = Interval([a], PL, DivItems([(a, False)]), substitution, C_R4)

ccp = ColorCaseProver()
ccp.set_statement("Theorem for E(3, 0; a, a, a+ 1).")

ccp.add_interval("D_1", D_1)

ccp.add_interval("B_1", B_1)
ccp.add_interval("B_2", B_2)
ccp.add_interval("B_3", B_3)
ccp.add_interval("B_4", B_4)

ccp.add_interval("R_1", R_1)
ccp.add_interval("R_2", R_2)

ccp.set_equation([1, 1, (1+1/a)])
ccp.set_substitution(substitution)

ccp.add_intervals_to_colour(0, ["D_1"])
ccp.add_intervals_to_colour(2, ["B_1"])
ccp.add_intervals_to_colour(2, ["B_2"])
ccp.add_intervals_to_colour(2, ["B_3"])
ccp.add_intervals_to_colour(2, ["B_4"])

ccp.add_intervals_to_colour(1, ["R_1"])
ccp.add_intervals_to_colour(1, ["R_2"])

cases = ccp.generate_cases(n)
ccp.generate_proof(cases)
