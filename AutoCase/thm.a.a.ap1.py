import sympy as sp
from filtered_interval import FilteredInterval
from filtered_intervals_colour_case_prover import FilteredIntervalsColorCaseProver
import pprint

# Symbolic variable
a = sp.Symbol("a", integer=True)

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

x_1, x_2, x_3 = sp.symbols("x_1 x_2 x_3", integer=True)
# Structural Lemmas 
###############################################################
cases = {
    'a': [('not_divides', a, x_1), ('not_divides', a, x_2), ('not_divides', a, x_3),],
    'b': [
        ('divides', a, x_1), ('divides', a, x_2), ('divides', a, x_3),
        ('not_divides', a**2, x_1), ('not_divides', a**2, x_2), ('not_divides', a**2, x_3),
    ],
    'c': [('divides', a**2, x_1), ('divides', a**2, x_2), ('not_divides', a, x_3),],
    'd': [('divides', a**2, x_1), ('not_divides', a, x_2), ('divides', a**2, x_3),],
    'e': [('not_divides', a, x_1), ('divides', a**2, x_2), ('divides', a**2, x_3),],
    'f': [('divides', a**2, x_1), ('not_divides', a, x_2), ('not_divides', a, x_3),],
    'g': [('not_divides', a, x_1), ('divides', a**2, x_2), ('not_divides', a, x_3),]
}

for c in cases:
    prover.add_contradiction_lemma(cases[c], "a.a.ap1")

prover.add_contradiction_lemma([('divides', a**2, x_1), ('divides', a**2, x_2), ('divides', a**2, x_3),], "a.a.ap1")
prover.add_contradiction_lemma([('not_divides', a, x_1), ('not_divides', a, x_2), ('divides', a**2, x_3),], "a.a.ap1")

# ----------------------------- S_a \ S_{a^2} Interval -----------------------------
D = FilteredInterval(symbols=[a])
D.set_assumptions(prover.assumptions)
D.set_bounds(a, a**4 + a**3 - a)
D.set_format_expression(a * (a + 1) * sp.Symbol("i") + a * sp.Symbol("j") + a, ["i", "j"])
D.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "a")})
D.add_must_divide(a)
D.add_must_not_divide(a**2)

prover.add_interval("D", D)
prover.add_interval_to_colour(0, "D")


# ----------------------------- R_l Interval -----------------------------

Rl = FilteredInterval(symbols=[a])
Rl.set_assumptions(prover.assumptions)
Rl.set_bounds(1, N)
Rl.set_format_expression(a * (a + 1) * sp.Symbol("i") + a * sp.Symbol("j") + sp.Symbol("k"), ["i", "j", "k"])
Rl.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "a"), "k": ("2*(j//2)+1", "a-1")})
Rl.add_must_not_divide(a)
prover.add_interval("R_l", Rl)
prover.add_interval_to_colour(1, "R_l")


# ----------------------------- R_r Intervals -----------------------------
Rr1 = FilteredInterval(symbols=[a])
Rr1.set_assumptions(prover.assumptions)
Rr1.set_bounds(a**4, a**4)
Rr1.add_must_divide(a**2)
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
Bl = FilteredInterval(symbols=[a])
Bl.set_assumptions(prover.assumptions)
Bl.set_bounds(1, N)
Bl.set_format_expression(a * (a + 1) * sp.Symbol("i") + a * sp.Symbol("j") + sp.Symbol("k"), ["i", "j", "k"])
Bl.set_format_ranges({"i": ("0", "a**2 - 1"), "j": ("0", "a"), "k": ("1", "2*(j//2)")})
Bl.add_must_not_divide(a)
prover.add_interval("B_l", Bl)
prover.add_interval_to_colour(2, "B_l")


# ----------------------------- B_r Intervals -----------------------------
Br1 = FilteredInterval(symbols=[a])
Br1.set_assumptions(prover.assumptions)
Br1.set_bounds(a**4 + a**2, a**4 + a**3 - a**2)
Br1.set_format_expression(a**4 + sp.Symbol("i") * a**2, ["i"])
Br1.set_format_ranges({"i": ("1", "a - 1")})
Br1.add_must_divide(a**2)
prover.add_interval("B_r1", Br1)
prover.add_interval_to_colour(2, "B_r1")


Br2 = FilteredInterval(symbols=[a])
Br2.set_assumptions(prover.assumptions)
Br2.set_bounds(a**3, a**4 - 2 * a**2)
Br2.set_format_expression(sp.Symbol("i") * a**3 + sp.Symbol("j") * a**2, ["i", "j"])
Br2.set_format_ranges({"i": ("1", "a - 1"), "j": ("0", "i - 1")})
Br2.add_must_divide(a**2)
prover.add_interval("B_r2", Br2)
prover.add_interval_to_colour(2, "B_r2")

Br3 = FilteredInterval(symbols=[a])
Br3.set_assumptions(prover.assumptions)
Br3.set_bounds(a**4/2 + a**2/2 + a**3, a**4 - a**2)
Br3.set_format_expression(sp.Symbol("i") * a**3 + sp.Symbol("i") * a**2, ["i"])
Br3.set_format_ranges({"i": ("(a + 1)//2", "a - 1")})
Br3.add_must_divide(a**2)
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


