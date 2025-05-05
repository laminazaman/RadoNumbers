import sympy as sp
from filtered_interval import FilteredInterval
from filtered_intervals_colour_case_prover import FilteredIntervalsColorCaseProver
import pprint

# Define symbolic variable and assumptions
a = sp.Symbol('a', integer=True, positive=True)
assumptions = [a >= 2]

# Define symbolic partitions
P0 = (1, a)
P1 = (a + 1, a**2 + 2*a)
P2 = (a**2 + 2*a + 1, a**2 + 3*a)
P3 = (a**2 + 3*a + 1, a**3 + 4*a**2 + 4*a)
P4 = (a**3 + 4*a**2 + 4*a + 1, a**3 + 4*a**2 + 5*a)
P5 = (a**3 + 4*a**2 + 5*a + 1, a**3 + 5*a**2 + 6*a)
P6 = (a**3 + 5*a**2 + 6*a + 1, a**3 + 5*a**2 + 7*a)

# Define total bound
n = a**3 + 5*a**2 + 7*a

# Define filtered intervals with symbolic bounds
D1 = FilteredInterval([a], bounds=P0)
D2 = FilteredInterval([a], bounds=P2)
D3 = FilteredInterval([a], bounds=P4)
D4 = FilteredInterval([a], bounds=P6)
R1 = FilteredInterval([a], bounds=P1)
R2 = FilteredInterval([a], bounds=P5)
B1 = FilteredInterval([a], bounds=P3)

# Initialize symbolic prover
prover = FilteredIntervalsColorCaseProver()
prover.set_equation([a, 1, 1])
prover.set_assumptions(assumptions)
prover.set_statement("Example: For a ≥ 2, R_3(E(3, 0; a, 1, 1)) ≥ a^3 + 5a^2 + 7a + 1.")

# Add intervals to the prover
prover.add_interval("D1", D1)
prover.add_interval("D2", D2)
prover.add_interval("D3", D3)
prover.add_interval("D4", D4)
prover.add_interval("R1", R1)
prover.add_interval("R2", R2)
prover.add_interval("B1", B1)

# Define colourings
prover.add_intervals_to_colour(0, ["D1", "D2", "D3", "D4"])  # Colour 0
prover.add_intervals_to_colour(1, ["R1", "R2"])              # Colour 1
prover.add_intervals_to_colour(2, ["B1"])                    # Colour 2

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

# Generate and prove all colour cases
colour_cases = prover.generate_cases(n)
print("Colour cases:")
print("----------------------------------------------------------------------------")
pprint.pprint(colour_cases)
print("----------------------------------------------------------------------------")
print()

prover.generate_proof(colour_cases)
