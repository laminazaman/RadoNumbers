import sympy as sp
from filtered_interval import FilteredInterval
from filtered_intervals_colour_case_prover import FilteredIntervalsColorCaseProver
import pprint

# Symbolic variable
a = sp.Symbol('a', integer=True)

# Create prover
prover = FilteredIntervalsColorCaseProver()
prover.set_statement("R₃(E(3,0;a,a,a+1)) ≥ a³(a+1)")

# Set equation
equation = [a, a, a+1]
prover.set_equation(equation)
assert prover.equation == equation and prover.equation not in [None, True, False], "Equation was not set properly"

prover.set_assumptions([sp.Ge(a, 7), sp.Ne(sp.Mod(a, 2), 0)])
assert prover.assumptions not in [[True], [False]], "Unexpectedly evaluated assumptions"

# N = a^3(a+1) - 1
N = sp.simplify(a**3 * (a + 1) - 1)


# ----------------------------- S_a \ S_{a^2} Interval -----------------------------
D = FilteredInterval([a])
D.set_assumptions(prover.assumptions)
D.set_bounds(a, a**4 + a**3 - a)
D.add_must_divide(a)
D.add_must_not_divide(a**2)

prover.add_interval("D", D)
prover.add_interval_to_colour(0, "D")


# ----------------------------- R_l Interval -----------------------------

"""
Rl = FilteredInterval(symbols=[a])
Rl.set_assumptions(prover.assumptions)
Rl.set_bounds(1, N)
Rl.set_format_expression(a * (a + 1) * sp.Symbol("i") + a * sp.Symbol("j") + sp.Symbol("k"), ["i", "j", "k"])
Rl.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "a"), "k": ("2*(j//2)+1", "a-1")})
Rl.add_must_not_divide(a)
prover.add_interval("R_l", Rl)
prover.add_interval_to_colour(1, "R_l")
"""

Rl_E = FilteredInterval(symbols=[a])
Rl_E.set_assumptions(prover.assumptions)
Rl_E.set_bounds(1, N)
Rl_E.set_format_expression(a * (a + 1) * sp.Symbol("i") + 2*a * sp.Symbol("j") + sp.Symbol("k"), ["i", "j", "k"])
Rl_E.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "(a-1)//2"), "k": ("2*j+1", "a-1")})
Rl_E.add_must_not_divide(a)
prover.add_interval("R_l_E", Rl_E)
prover.add_interval_to_colour(1, "R_l_E")

Rl_O = FilteredInterval(symbols=[a])
Rl_O.set_assumptions(prover.assumptions)
Rl_O.set_bounds(1, N)
Rl_O.set_format_expression(a * (a + 1) * sp.Symbol("i") + 2*a * sp.Symbol("j") + a + sp.Symbol("k"), ["i", "j", "k"])
Rl_O.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "(a-1)//2"), "k": ("2*j+1", "a-1")})
Rl_O.add_must_not_divide(a)
prover.add_interval("R_l_O", Rl_O)
prover.add_interval_to_colour(1, "R_l_O")

# ----------------------------- R_r Intervals -----------------------------
Rr1 = FilteredInterval(symbols=[a])
Rr1.set_assumptions(prover.assumptions)
Rr1.set_bounds(a**4, a**4)
Rr1.add_must_divide(a**4)
Rr1.set_format_expression(sp.Symbol("i") * a**4, ["i"])
Rr1.set_format_ranges({"i" : ("1", "1")})
prover.add_interval("R_r1", Rr1)
prover.add_interval_to_colour(1, "R_r1")


Rr2 = FilteredInterval(symbols=[a])
Rr2.set_assumptions(prover.assumptions)
Rr2.set_bounds(a**2, a**4-a**2)
Rr2.set_format_expression(sp.Symbol("i") * a**3 + sp.Symbol("j") * a**2, ["i", "j"])
Rr2.set_format_ranges({"i": ("0", "a - 1"), "j": ("i + 1", "a - 1")})
Rr2.add_must_divide(a**2)
Rr2.add_must_not_divide(a**3)

prover.add_interval("R_r2", Rr2)
prover.add_interval_to_colour(1, "R_r2")


Rr3 = FilteredInterval(symbols=[a])
Rr3.set_assumptions(prover.assumptions)
Rr3.set_bounds(a**3 + a**2, a**4 - a**2)
Rr3.set_format_expression(sp.Symbol("i") * a**3 + sp.Symbol("i") * a**2, ["i"])
Rr3.set_format_ranges({"i": ("1", "(a - 1)//2")})
Rr3.add_must_divide(a**2)
Rr3.add_must_not_divide(a**3)

prover.add_interval("R_r3", Rr3)
prover.add_interval_to_colour(1, "R_r3")


# ----------------------------- B_l Interval -----------------------------
"""
Bl = FilteredInterval(symbols=[a])
Bl.set_assumptions(prover.assumptions)
Bl.set_bounds(1, N)
Bl.set_format_expression(a * (a + 1) * sp.Symbol("i") + a * sp.Symbol("j") + sp.Symbol("k"), ["i", "j", "k"])
Bl.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "a"), "k": ("1", "2*(j//2)")})
Bl.add_must_not_divide(a)
prover.add_interval("B_l", Bl)
prover.add_interval_to_colour(2, "B_l")
"""

Bl_E = FilteredInterval(symbols=[a])
Bl_E.set_assumptions(prover.assumptions)
Bl_E.set_bounds(1, N)
Bl_E.set_format_expression(a * (a + 1) * sp.Symbol("i") + 2*a * sp.Symbol("j") + sp.Symbol("k"), ["i", "j", "k"])
Bl_E.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "(a-1)//2"), "k": ("1", "2*j")})
Bl_E.add_must_not_divide(a)
prover.add_interval("B_l_E", Bl_E)
prover.add_interval_to_colour(2, "B_l_E")

Bl_O = FilteredInterval(symbols=[a])
Bl_O.set_assumptions(prover.assumptions)
Bl_O.set_bounds(1, N)
Bl_O.set_format_expression(a * (a + 1) * sp.Symbol("i") + 2*a * sp.Symbol("j") + a + sp.Symbol("k"), ["i", "j", "k"])
Bl_O.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "(a-1)//2"), "k": ("1", "2*j")})
Bl_O.add_must_not_divide(a)
prover.add_interval("B_l_O", Bl_O)
prover.add_interval_to_colour(2, "B_l_O")

# ----------------------------- B_r Intervals -----------------------------
Br1 = FilteredInterval(symbols=[a])
Br1.set_assumptions(prover.assumptions)
Br1.set_bounds(a**4 + a**2, a**4 + a**3 - a**2)
Br1.set_format_expression(a**4 + sp.Symbol("i") * a**2, ["i"])
Br1.set_format_ranges({"i": ("1", "a - 1")})
Br1.add_must_divide(a**2)
Br1.add_must_not_divide(a**4)
prover.add_interval("B_r1", Br1)
prover.add_interval_to_colour(2, "B_r1")


Br2 = FilteredInterval(symbols=[a])
Br2.set_assumptions(prover.assumptions)
Br2.set_bounds(a**3, a**4 - 2 * a**2)
Br2.set_format_expression(sp.Symbol("i") * a**3 + sp.Symbol("j") * a**2, ["i", "j"])
Br2.set_format_ranges({"i": ("1", "a - 1"), "j": ("0", "i - 1")})
Br2.add_must_divide(a**2)
Br2.add_must_not_divide(a**4)

prover.add_interval("B_r2", Br2)
prover.add_interval_to_colour(2, "B_r2")

Br3 = FilteredInterval(symbols=[a])
Br3.set_assumptions(prover.assumptions)
Br3.set_bounds(a**4/2 + a**2/2 + a**3, a**4 - a**2)
Br3.set_format_expression(sp.Symbol("i") * a**3 + sp.Symbol("i") * a**2, ["i"])
Br3.set_format_ranges({"i": ("(a + 1)//2", "a - 1")})
Br3.add_must_divide(a**2)
Br3.add_must_not_divide(a**3)
prover.add_interval("B_r3", Br3)
prover.add_interval_to_colour(2, "B_r3")

print("Prover setup:")
print("----------------------------------------------------------------------------")
pprint.pprint(prover.get())
print("----------------------------------------------------------------------------")
print()


print("Partition check:")
print("----------------------------------------------------------------------------")
prover.check_partition(N)
print("----------------------------------------------------------------------------")
print()

colour_cases = prover.generate_cases(N)
print("Colour cases:")
print("----------------------------------------------------------------------------")
pprint.pprint(colour_cases)
print("----------------------------------------------------------------------------")
print()

prover.generate_proof(colour_cases)


