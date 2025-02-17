import sympy as sp

class Constraint:
    def __init__(self, function, ranges, to_be_satisfied, subs):
        self.function = function
        self.ranges = ranges
        self.to_be_satisfied = to_be_satisfied
        self.subs = subs
        self.numeric_set = self.get_constraint_numeric_set()
    
    def get(self):
        return {
            'function': self.function,
            'ranges': self.ranges,
            'to_be_satisfied': self.to_be_satisfied
        }

    def get_items(self, exp):
        items = {}
        terms = exp.as_ordered_terms()
        for term in terms:
            coeff_mul = term.as_coeff_Mul()
            items[str(coeff_mul[1])] = coeff_mul[0]
        return items
    
    def get_matched_items(self, items):
        matched_items = dict()
        for item in items:
            matched_items[item] = items[item]
        for fun in self.function:
            if fun not in matched_items:
                matched_items[fun] = 0
                items[fun] = 0
        return matched_items, (len(items)==len(matched_items))

    def subs_range(self, var, subs):
        start = self.ranges[var][0]
        end = self.ranges[var][1]
        if not isinstance(self.ranges[var][0], int):
            start = self.ranges[var][0].subs(subs)
        if not isinstance(self.ranges[var][1], int):
            end = self.ranges[var][1].subs(subs)
        return [start, end]

    def get_constraint_numeric_set(self):
        new_range = {}
        S = set()
        r_keys = list(self.ranges.keys())
        length = len(r_keys)

        current_subs = self.subs
        if length == 1:
            i = r_keys[0]
            i_range = self.subs_range(i, current_subs)
            f = 0
            for x in self.function:
                f += self.function[x][1] * self.function[x][0]
            for i_val in range(i_range[0], i_range[1]+1):
                S.add(f.subs({i: i_val}).subs(self.subs))
            return S
        elif length == 2:
            i = r_keys[0]
            i_range = self.subs_range(i, current_subs)
            f = 0
            for x in self.function:
                f += self.function[x][1] * self.function[x][0]
            for i_val in range(i_range[0], i_range[1]+1):
                j = r_keys[1]
                current_subs.update({i : i_val})
                j_range = self.subs_range(j, current_subs)
                for j_val in range(j_range[0], j_range[1]+1):
                    S.add(f.subs({j: j_val}).subs(self.subs))
            return S
        elif length == 3:
            i = r_keys[0]
            i_range = self.subs_range(i, current_subs)
            f = 0
            for x in self.function:
                f += self.function[x][1] * self.function[x][0]
            for i_val in range(i_range[0], i_range[1]+1):
                j = r_keys[1]
                current_subs.update({i : i_val})
                j_range = self.subs_range(j, current_subs)
                for j_val in range(j_range[0], j_range[1]+1):
                    k = r_keys[2]
                    current_subs.update({j : j_val})
                    k_range = self.subs_range(k, current_subs)
                    
                    for k_val in range(k_range[0], k_range[1]+1):
                        #print(f"{i_val}, {j_val}, {k_val}")
                        S.add(f.subs({k: k_val}).subs(self.subs))
            return S


    def satisfied(self, exp):
        if isinstance(exp, int):
            sexp = exp
        else:
            sexp = exp.subs(self.subs)

        if self.to_be_satisfied:
            if sexp in self.numeric_set:
                return True
            else:
                return False
        else:
            if sexp not in self.numeric_set:
                return True
            else:
                return False

