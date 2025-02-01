from sympy import symbols, Interval, ConditionSet, ImageSet 
from sympy import And, Mod, simplify, Lambda, denom
import pprint
from interval_checker import IntervalChecker

# Define variables
a, b, v, k = symbols('a b v k', integer=True, positive=True)

# Define P_0, P_1, P_2, P_3, and P_4 as an interval
P0 = Interval(1, a * b)
P1 = Interval(b*a + 1, b**2 * a)
P2 = Interval(b**2 * a + 1, b * a**2 + b * a)
P3 = Interval(b * a**2 + b * a + 1, a**3 + a**2 + (b + 1) * a)
P4 = Interval(a**3 + a**2 + (b + 1) * a + 1, a**3 + a**2 + (2 * b + 1) * a)

R1 = {
    'interval': P0,
    'not_divisible_by': b,
    'multiple_of_b_exists': False,
    'multiple_of_bsq_exists': False,
    'start': P0.start,
    'end': P0.end,
}

R2 = {
    'interval': Interval(1, b**2 * a), 
    'divisible_by': b**2, 
    'multiple_of_b_exists': True,
    'multiple_of_bsq_exists': True,
    'start': b**2,
    'end': b**2 * a,
}

R3 = {
    'interval': P4, 
    'multiple_of_b_exists': True,
    'multiple_of_bsq_exists': True,
    'start': P4.start,
    'end': P4.end,
}

B1 = {
    'interval': Interval(1, b**2 * a), 
    'divisible_by': b,
    'not_divisible_by': b**2, 
    'multiple_of_b_exists': True,
    'multiple_of_bsq_exists': False,
    'start': b,
    'end': b**2 * a,
}

B2 = {
    'interval': P2, 
    'divisible_by': b,
    'multiple_of_b_exists': True,
    'multiple_of_bsq_exists': True,
    'start': b**2 * a + b,
    'end': b * a**2 + b * a,
}

D1 = {
    'interval': Interval(b * a + 1, b * a**2 + b * a), 
    'not_divisible_by': b,
    'multiple_of_b_exists': False,
    'multiple_of_bsq_exists': False,
    'start': b * a + 1,
    'end': b * a**2 + b * a,
}

D2 = {
    'interval': P3, 
    'multiple_of_b_exists': True,
    'multiple_of_bsq_exists': True,
    'start': P3.start-1+b,
    'end': P3.end,
}



ic = IntervalChecker()
ic.add_interval("R1", R1)
ic.add_interval("R2", R2)
ic.add_interval("R3", R3)
ic.add_interval("B1", B1)
ic.add_interval("B2", B2)
ic.add_interval("D1", D1)
ic.add_interval("D2", D2)


def generate_cases(filtered_set_names):
    case = []
    for i in range(len(filtered_set_names)):
        for j in range(len(filtered_set_names)):
            x_interval_name = filtered_set_names[i]
            if ic.intervals[x_interval_name]['multiple_of_b_exists'] == False:
                continue
            y_interval_name = filtered_set_names[j]

            xy_intervals = [x_interval_name, y_interval_name]
            earliest_interval = sorted(xy_intervals)[0]
            z_intervals = [filtered_set_names[i] for i in range(len(filtered_set_names)) if filtered_set_names[i]>=earliest_interval]
            case.append([x_interval_name, y_interval_name, z_intervals])
    return case

colour_cases = {
    0: generate_cases(["D1", "D2"]),
    1: generate_cases(["R1", "R2", "R3"]),
    2: generate_cases(["B1", "B2"])
}

equation = [a/b, 1, 1]

output = dict()
output_verified = True
for colour_case in colour_cases:
    output[colour_case] = []
    for case in colour_cases[colour_case]:
        x_lower = ic.intervals[case[0]]['start']
        y_lower = ic.intervals[case[1]]['start']

        x_upper = ic.intervals[case[0]]['end']
        y_upper = ic.intervals[case[1]]['end']

        lb = simplify(equation[0] * x_lower + equation[1] * y_lower)
        ub = simplify(equation[0] * x_upper + equation[1] * y_upper)
        
        z_lower = simplify(lb / equation[2])
        z_upper = simplify(ub / equation[2])

        subcase = {
            'x' : {'in': case[0], 'range': ic.intervals[case[0]]['interval']},
            'y' : {'in': case[1], 'range': ic.intervals[case[1]]['interval']},
            'z' : {
                '>=': z_lower,
                '<=': z_upper,
                'in': dict()
                },
            'c' : []

        }
        
        for case2 in case[2]:
            interval = ic.intervals[case2]['interval']

            solution_exists = True
            divisibility_check = True
            non_divisibility_check = True

            ######################################################
            z_LB_beyond_interval = ic.z_LB_beyond_interval(z_lower, case2, {a:4, b:3})
            if z_LB_beyond_interval == True:
                end = interval.end if isinstance(interval, Interval) else interval['end']
                argument = f"z not in {case2}: z >= {z_lower} > {end} = max({case2})"
                subcase['c'].append(argument)

            solution_exists = solution_exists & (not z_LB_beyond_interval)

            ######################################################
            z_UB_before_interval = ic.z_UB_before_interval(z_upper, case2, {a:4, b:3})
            if z_UB_before_interval == True:
                start = interval.start if isinstance(interval, Interval) else interval['start']
                argument = f"z not in {case2}: z <= {z_upper} < {start} = min({case2})"
                subcase['c'].append(argument)

            solution_exists = solution_exists & (not z_UB_before_interval)

            ######################################################
            z_lower_divisible_by = ic.z_divisible_by(z_lower, case2)
            if z_lower_divisible_by == False:
                divby = ic.intervals[case2]['divisible_by']
                argument = f"z not in {case2}: {z_lower} is not divisible by {divby}"
                subcase['c'].append(argument)

            solution_exists = solution_exists & (z_lower_divisible_by)

            
            z_lower_not_divisible_by = ic.z_not_divisible_by(z_lower, case2)
            if z_lower_not_divisible_by == False:
                divby = ic.intervals[case2]['not_divisible_by']
                argument = f"z not in {case2}: {z_lower} is divisible by {divby}"
                subcase['c'].append(argument)

            solution_exists = solution_exists & (z_lower_not_divisible_by)
            

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
