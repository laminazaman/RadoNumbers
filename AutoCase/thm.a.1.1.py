from sympy import symbols, Eq, simplify, solve, Interval, And
from interval_checker import IntervalChecker
import pprint

a, x, y, z = symbols('a x y z', positive=True, integer=True)

ic = IntervalChecker()
ic.add_interval("P0", Interval(1, a))
ic.add_interval("P1", Interval(a+1, a**2 + 2*a))
ic.add_interval("P2", Interval(a**2 + 2*a + 1, a**2 + 3*a))
ic.add_interval("P3", Interval(a**2 + 3*a + 1, a**3 + 4*a**2 + 4*a))
ic.add_interval("P4", Interval(a**3 + 4*a**2 + 4*a + 1, a**3 + 4*a**2 + 5*a))
ic.add_interval("P5", Interval(a**3 + 4*a**2 + 5*a + 1, a**3 + 5*a**2 + 6*a))
ic.add_interval("P6", Interval(a**3 + 5*a**2 + 6*a + 1, a**3 + 5*a**2 + 7*a))


equation = [a, 1, 1]
threshold = 1

def generate_cases(interval_names):
    case = []
    for i in range(len(interval_names)):
        for j in range(len(interval_names)):
            x_interval_name = interval_names[i]
            y_interval_name = interval_names[j]

            xy_intervals = [x_interval_name, y_interval_name]
            earliest_interval = sorted(xy_intervals)[0]
            z_intervals = [interval_names[i] for i in range(len(interval_names)) if interval_names[i]>=earliest_interval]
            case.append([x_interval_name, y_interval_name, z_intervals])
    return case

colour_cases = {
    0: generate_cases(["P0", "P2", "P4", "P6"]),
    1: generate_cases(["P1", "P5"]),
    2: generate_cases(["P3"])
}

output = dict()
output_verified = True
for colour_case in colour_cases:
    output[colour_case] = []
    for case in colour_cases[colour_case]:
        x_lower = ic.intervals[case[0]].start
        y_lower = ic.intervals[case[1]].start

        x_upper = ic.intervals[case[0]].end
        y_upper = ic.intervals[case[1]].end

        lb = simplify(equation[0] * x_lower + equation[1] * y_lower)
        ub = simplify(equation[0] * x_upper + equation[1] * y_upper)
        
        z_lower = simplify(lb / equation[2])
        z_upper = simplify(ub / equation[2])

        subcase = {
            'x' : {'in': case[0], 'range': [ic.intervals[case[0]].start, ic.intervals[case[0]].end]},
            'y' : {'in': case[1], 'range': [ic.intervals[case[1]].start, ic.intervals[case[1]].end]},
            'z' : {
                '>=': z_lower,
                '<=': z_upper,
                'in': dict()
                },
            'c' : []
        }

        for case2 in case[2]:
            interval = ic.intervals[case2]

            solution_exists = True
            ######################################################
            z_LB_beyond_interval = ic.z_LB_beyond_interval(z_lower, case2, {a:1})
            if z_LB_beyond_interval == True:
                end = interval.end if isinstance(interval, Interval) else interval['end']
                argument = f"z not in {case2}: z >= {z_lower} > {end} = max({case2})"
                subcase['c'].append(argument)

            solution_exists = solution_exists & (not z_LB_beyond_interval)

            ######################################################
            z_UB_before_interval = ic.z_UB_before_interval(z_upper, case2, {a:1})
            if z_UB_before_interval == True:
                start = interval.start if isinstance(interval, Interval) else interval['start']
                argument = f"z not in {case2}: z <= {z_upper} < {start} = min({case2})"
                subcase['c'].append(argument)

            solution_exists = solution_exists & (not z_UB_before_interval)


            subcase['z']['in'][case2] = solution_exists 
            if subcase['z']['in'][case2] == True:
                output_verified = False
        output[colour_case].append(subcase)

print("Intervals:")
pprint.pprint(ic.intervals)

print("\nColour Cases:")
pprint.pprint(colour_cases)

print("\nProof:")
pprint.pprint(output)
print(f"\nTheorem proven: {output_verified}")


