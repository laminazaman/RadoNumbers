from sympy import symbols, Eq, simplify, solve, Interval, And, denom, Mod

class IntervalChecker:
    def __init__(self):
        self.intervals = {}
    
    def add_interval(self, name, interval, zero_modulo_filter=None, nonzero_modulo_filter=None):
        self.intervals[name] = interval
        
    def z_LB_beyond_interval(self, z_lower, interval_name, substitution):
        interval = self.intervals[interval_name]
        if isinstance(interval, Interval):
            texp = simplify(z_lower - interval.end)
        else:
            texp = simplify(z_lower - interval['end'])
        if texp.subs(substitution) >= 0:
            return True
        return False

    def z_UB_before_interval(self, z_upper, interval_name, substitution):
        interval = self.intervals[interval_name]
        if isinstance(interval, Interval):
            texp = simplify(interval.start - z_upper)
        else:
            texp = simplify(interval['start'] - z_upper)
        if texp.subs(substitution) >= 0:
            return True
        return False

    def z_divisible_by(self, z, interval_name):
        interval = self.intervals[interval_name]
        if isinstance(interval, Interval):
            return True
        else:
            if 'divisible_by' not in interval:
                return True
            else:
                return (simplify(Mod(z, interval['divisible_by']) == 0))    

    def z_not_divisible_by(self, z, interval_name):
        interval = self.intervals[interval_name]
        if isinstance(interval, Interval):
            return True
        else:
            if 'not_divisible_by' not in interval:
                return True
            else:
                return (simplify(Mod(z, interval['not_divisible_by'])) != 0) 