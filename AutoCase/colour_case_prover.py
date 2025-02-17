import sympy as sp
from itertools import product
from interval import Interval
from divisibility import Divisibility
import pprint

class ColorCaseProver:
    def __init__(self):
        self.intervals = dict()
        self.colouring = dict()
        self.equation = list()
        self.substitution = {}
        self.divisibility = Divisibility({})
        self.statement = ""

    def clear(self):
        self.intervals.clear()
        self.colouring.clear()
        self.equation.clear()

    def add_interval(self, name, interval):
        self.intervals[name] = interval

    def add_interval_to_colour(self, c, name):
        if c not in self.colouring:
            self.colouring[c] = [name]
        else:
            self.colouring[c].append(name)
    
    def add_intervals_to_colour(self, c, names):
        for name in names:
            self.add_interval_to_colour(c, name)

    def get(self):
        return {
            'intervals': {interval: self.intervals[interval].get() for interval in self.intervals},
            'colouring': self.colouring,
            'equation': self.equation,
        }        

    def set_equation(self, eq):
        self.equation = eq

    def set_substitution(self, subs):
        self.substitution = subs
        self.divisibility.set_subs(subs)

    def set_statement(self, statement):
        self.statement = statement

    def generate_variable_containments(self, m, t):
        # Generate all possible containments of (m-1) variables among t sets
        containments = list(product(range(t), repeat=m-1))    
        return containments

    def is_feasible(self, col, containment):
        for i in range(len(containment)):
            eq_denom = sp.denom(self.equation[i])
            if eq_denom != 1:
                interval = self.intervals[self.colouring[col][containment[i]]].get()
                if (eq_denom, False) in interval['divitems']:
                    return False
        return True

    def generate_colour_cases(self, col):
        m = len(self.equation)
        t = len(self.colouring[col])
        containments = self.generate_variable_containments(m, t)
        cases = []
        for c in containments:
            if self.is_feasible(col, c) == False:
                continue
            lhs_intervals = [self.colouring[col][c[i]] for i in range(len(c))]
            earliest_interval = sorted(lhs_intervals)[0]
            z_intervals = [self.colouring[col][i] for i in range(len(self.colouring[col])) if self.colouring[col][i]>=earliest_interval]
            case = [tuple(lhs_intervals), z_intervals]
            cases.append(case)
        return cases

    def generate_cases(self, n):
        
        if self.covers_the_overall_interval(n) == False:
            print("Partition does not seem to be correct!")
            exit(0)
        else:
            print("Partition is correct!")
            
        colours = list(self.colouring.keys())
        cases = {
            colours[i] : self.generate_colour_cases(colours[i]) for i in range(len(colours))
        }        
        return cases


    def generate_proof(self, colour_cases):
        output = dict()
        output_verified = True
        for colour_case in colour_cases:
            output[colour_case] = []
            for case in colour_cases[colour_case]:
                lhs_intervals = case[0]

                z_min_array = [self.intervals[lhs_intervals[i]].get_min() * self.equation[i] for i in range(len(lhs_intervals))]
                z_min = sp.simplify(sp.Add(*z_min_array) / self.equation[-1])

                z_max_array = [self.intervals[lhs_intervals[i]].get_max() * self.equation[i] for i in range(len(lhs_intervals))]
                z_max = sp.simplify(sp.Add(*z_max_array) / self.equation[-1])
        
                subcase = dict()
                for i in range(1, len(lhs_intervals)+1):
                    subcase[f"x_{i}"] = {
                        'in': lhs_intervals[i-1], 
                        'range': self.intervals[lhs_intervals[i-1]].get()['interval']
                        }
                subcase[f"x_{len(lhs_intervals)+1}"] = {
                    '>=': z_min,
                    '<=': z_max,
                    'in': dict()
                }
                subcase['a'] = []
                for case2 in case[1]:
                    interval = self.intervals[case2].get()['interval']
                    solution_exists = True
                    divisibility_check = True
                    non_divisibility_check = True

                    z_min_above_the_upper_bound = self.intervals[case2].above_the_upper_bound(z_min)
                    if z_min_above_the_upper_bound == True:
                        end = self.intervals[case2].get_max()
                        argument = f"x_{len(lhs_intervals)+1} not in {case2}: x_{len(lhs_intervals)+1} >= {z_min} > {end} = max({case2})"
                        subcase['a'].append(argument)

                    solution_exists = solution_exists & (not z_min_above_the_upper_bound)

                    z_max_below_the_lower_bound = self.intervals[case2].below_the_lower_bound(z_max)
                    if z_max_below_the_lower_bound == True:
                        start = self.intervals[case2].get_min()
                        argument = f"x_{len(lhs_intervals)+1} not in {case2}: x_{len(lhs_intervals)+1} <= {z_max} < {start} = min({case2})"
                        subcase['a'].append(argument)

                    solution_exists = solution_exists & (not z_max_below_the_lower_bound)

                    case2_divitems = self.intervals[case2].get_divitems()

                    satisfies = self.divisibility.satisfies(z_min, case2_divitems)
                    if satisfies[0] == False:
                        item = satisfies[1]
                        text = "not an integer multiple" if item[1]==True else "an integer multiple"
                        argument = f"x_{len(lhs_intervals)+1} not in {case2}: {z_min} is {text} of {satisfies[1][0]}"
                        subcase['a'].append(argument)

                    solution_exists = solution_exists & (satisfies[0])

                    if self.intervals[case2].constraint != None:    
                        constraint = self.intervals[case2].constraint
                        if constraint.to_be_satisfied == True:
                            if not constraint.satisfied(z_min):
                                text = f"not an element of the format {constraint.function}"
                                argument = f"x_{len(lhs_intervals)+1} not in {case2}: {z_min} is {text}"
                                subcase['a'].append(argument)
                        else:
                            if constraint.satisfied(z_min):
                                text = f"an element of the format {constraint.function}"
                                argument = f"x_{len(lhs_intervals)+1} not in {case2}: {z_min} is {text}"
                                subcase['a'].append(argument)

                    elif self.intervals[case2].constraints != None:
                        constraints = self.intervals[case2].constraints
                        satisfies_constraint = True
                        if constraints != None:
                            for c in range(len(constraints)):
                                satisfies_constraint = satisfies_constraint and constraints[c].satisfied(z_min)
                        if satisfies_constraint == False:
                            text = f"does not satisfy constraints"
                            argument = f"x_{len(lhs_intervals)+1} not in {case2}: {z_min} {text}"
                            subcase['a'].append(argument)

                    #solution_exists = solution_exists & (rhs_is_integer)

                    z_is_integer = self.divisibility.is_integral(z_min)
                    if z_is_integer == False:
                        argument = f"z is not an integer"
                        subcase['a'].append(argument)
                    solution_exists = solution_exists & (z_is_integer)

                    rhs_is_integer = self.divisibility.rhs_is_integral(self.equation[-1], case2_divitems)
                    if rhs_is_integer == False:
                        argument = f"The RHS is not an integer"
                        subcase['a'].append(argument)
                    solution_exists = solution_exists & (rhs_is_integer)

                    subcase[f'x_{len(lhs_intervals)+1}']['in'][case2] = solution_exists
                    if subcase[f'x_{len(lhs_intervals)+1}']['in'][case2] == True:
                        output_verified = False
                
                output[colour_case].append(subcase)

        print(f"{self.statement}\n")
        pprint.pprint(output)
        print(f"\nAll cases led to contradiction?: {output_verified}")
    
    def covers_the_overall_interval(self, n_exp):
        n = n_exp.subs(self.substitution)
        colours = list(self.colouring.keys())
        colour_sets = dict()
    
        union_set = set()
        counter = {i : 0 for i in range(1, n+1)}
        contained = {i : [] for i in range(1, n+1)}
        at_most_one_colour_per_integer = True

        for i in range(len(colours)):
            colour_sets[colours[i]] = set()
            for j in range(len(self.colouring[i])):
                interval = self.intervals[self.colouring[i][j]]
                start = interval.get_min().subs(self.substitution)
                end = interval.get_max().subs(self.substitution)
                divitems = interval.get_divitems()
                constraint = interval.constraint
                constraints = interval.constraints
    
                for k in range(start, end+1):
                    satisfies_divisibility, item_ = self.divisibility.satisfies(k, divitems)
                    satisfies_constraint = True
                    if constraint != None:
                        satisfies_constraint = constraint.satisfied(k)                        
                    elif constraints != None:
                        for c in range(len(constraints)):
                            satisfies_constraint = satisfies_constraint and constraints[c].satisfied(k)

                    if satisfies_divisibility and satisfies_constraint:
                        colour_sets[colours[i]].add(k)
                        contained[k].append(colours[i])
                        counter[k] += 1
                        if counter[k] > 1:
                            at_most_one_colour_per_integer = False
                        union_set.add(k)
                        
        partition_verified = (n == len(union_set)) and at_most_one_colour_per_integer
        return partition_verified


    