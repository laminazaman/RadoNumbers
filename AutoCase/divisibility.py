import sympy as sp
from divitems import DivItems


class Divisibility:
    def __init__(self, substitution):
        self.substitution = substitution
        
    def set_subs(self, substitution):
        self.substitution = substitution

    def rhs_is_integral(self, exp, divitems=[]):
        texp = sp.simplify(exp)
        if texp.is_integer:
            return True
        else:
            for item in divitems:
                if item[1]==True:
                    # Since z has item[0] as a factor 
                    texp = texp * item[0]
                    if texp.is_integer:
                        return True
            return False

    def is_integral(self, exp, divitems=[]):
        texp = sp.simplify(exp)
        sexp = texp.subs(self.substitution)
        return sexp.is_integer        

    def satisfies(self, exp, divitems=[]):
        for item in divitems:
            if item[1]==True:
                r = sp.simplify(sp.Mod(exp, item[0]))
                r_subs = r.subs(self.substitution)                 
                if r_subs != 0:
                    return False, item
            else:
                r = sp.simplify(sp.Mod(exp, item[0]))
                r_subs = r.subs(self.substitution) 
                if r_subs == 0:
                    return False, item
        return True, None