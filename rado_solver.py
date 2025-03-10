# multiple colours, three terms

from pysat.solvers import Solver, Cadical153
import math
import sys
import time

k = 3 # number of colours
n = 1 # counter
start = 1 # starting point

# equation: ax + by = cz
a = int(sys.argv[1])
b = int(sys.argv[2])
c = int(sys.argv[3])

# fix colours for 2, 3, 4, ...
fixed = []
n_fixed = len(fixed)
s = ".".join(map(str, fixed))

# filenames
if n_fixed == 0:
    log_name = f"cadical_log/log/log_{a}.{b}.{c}_{n_fixed}.txt"
    sat_name = f"cadical_log/sat/sat_{a}.{b}.{c}_{n_fixed}.txt"
else:
    log_name = f"cadical_log/log/log_{a}.{b}.{c}_{n_fixed}_{s}.txt"
    sat_name = f"cadical_log/sat/sat_{a}.{b}.{c}_{n_fixed}_{s}.txt"

start_time = time.time()
number_colouring = "None"
exponent_colouring = "None"

# return mapped variable (integer from [1, k * n])
# col = colour of variable, pos = position of variable
def mapped_variable(col, pos):
    return (pos - 1) * k + col

# return colour of variable (integer from [1, k])
# var = mapped variable
def variable_colour(var):
    if var % k == 0:
        return k
    else:
        return var % k

# return position of variable (integer from [1, n])
# var = mapped variable
def variable_position(var):
    return math.ceil(var / k)

# one position can be any of the given colours
def positive_clause(pos):
    clause = []
    for i in range(1, k + 1):
        clause.append(mapped_variable(i, pos))
    return clause

# three specified positions don't form a monochromatic solution
def negative_clause(col, x, y, z):
    clause = []
    clause.append(mapped_variable(col, x))
    clause.append(mapped_variable(col, y))
    clause.append(mapped_variable(col, z))
    clause = [-i for i in clause]
    return clause

# one position is assigned at most one colour
def optional_clause(i, j, pos):
    clause = []
    clause.append(mapped_variable(i, pos))
    clause.append(mapped_variable(j, pos))
    clause = [-i for i in clause]
    return clause

# symmetry breaking clauses

def integer_1_is_colour_1():
    clauses = []
    clauses.append([mapped_variable(1, 1)])
    return clauses

def colour_3_cannot_appear_before_colours_1_2(n):
    clause = []
    for j in range(1, n):
        clause.append(-mapped_variable(1, j))
    clause.append(-mapped_variable(3, n))
    return clause

# extended Euclidean algorithm
def eea(a, b):
    r1, r2 = a, b
    x1, x2 = 1, 0
    y1, y2 = 0, 1

    while r2 != 0:
        q = r1 // r2
        r1, r2 = r2, r1 - q * r2
        x1, x2 = x2, x1 - q * x2
        y1, y2 = y2, y1 - q * y2

    return x1, y1, r1

# return list of x, y, z values that satisfy ax + by = c
def diophantine_solutions(a, b, c):
    x0, y0, gcd = eea(abs(a), abs(b))
    sols = []

    if c % gcd != 0:
        return sols

    x0 *= c // gcd
    y0 *= c // gcd

    if a < 0:
        x0 *= -1
    if b < 0:
        y0 *= -1

    if a > 0 and b > 0:
        start = max((1 - x0) * gcd / b, (y0 - n) * gcd / a)
        end = min((n - x0) * gcd / b, (y0 - 1) * gcd / a)
    elif a > 0 and b < 0:
        start = max((n - x0) * gcd / b, (y0 - n) * gcd / a)
        end = min((1 - x0) * gcd / b, (y0 - 1) * gcd / a)
    elif a < 0 and b > 0:
        start = max((1 - x0) * gcd / b, (y0 - 1) * gcd / a)
        end = min((n - x0) * gcd / b, (y0 - n) * gcd / a)
    elif a < 0 and b < 0:
        start = max((n - x0) * gcd / b, (y0 - 1) * gcd / a)
        end = min((1 - x0) * gcd / b, (y0 - n) * gcd / a)

    start = math.ceil(start)
    end = math.floor(end)

    for k in range(start, end + 1):
        x = x0 + k * (b // gcd)
        y = y0 - k * (a // gcd)
        sols.append((x, y))

    return sols

# return list of x, y, z values that satisfy ax + by = cz
def solve_equation(n):
    solutions = set()
    
    x = n
    sols = diophantine_solutions(-b, c, a*n)
    for sol in sols:
        y = sol[0]
        z = sol[1]
        if a*x + b*y == c*z and 1 <= y and y <= n and 1 <= z and z <= n:
            solutions.add((x, y, z))

    if a != b:
        y = n
        sols = diophantine_solutions(-a, c, b*n)
        for sol in sols:
            x = sol[0]
            z = sol[1]
            if a*x + b*y == c*z and 1 <= x and x <= n and 1 <= z and z <= n:
                solutions.add((x, y, z))

    z = n
    sols = diophantine_solutions(a, b, c*n)
    for sol in sols:
        x = sol[0]
        y = sol[1]
        if a*x + b*y == c*z and 1 <= x and x <= n and 1 <= y and y <= n:
            solutions.add((x, y, z))

    return solutions

# check satisfying assignment for correctness
def check(model):
    n = len(model)
    # an exhaustive search for monochromatic solutions of ax + by = cz
    for i in range(1,n+1):
        for j in range(1,n+1):
            if model[i-1] == model[j-1]:
                zc = a*i + b*j
                yb = c*j - a*i
                xa = c*j - b*i
                if zc//c in range(1,n+1) and zc % c == 0 and model[zc//c-1] == model[i-1]:
                    return f"Monochromatic Solution ({i}, {j}, {zc//c}) Found"
                if yb//b in range(1,n+1) and yb % b == 0 and model[yb//b-1] == model[i-1]:
                    return f"Monochromatic Solution ({i}, {yb//b}, {j}) Found"
                if xa//a in range(1,n+1) and xa % a == 0 and model[xa//a-1] == model[i-1]:
                    return f"Monochromatic Solution ({xa//a}, {i}, {j}) Found"
    return ""
    
# converts model to numbers (0, 1, 2)
def toNumbers(model):
    assert(len(model) % k == 0)
    cols = ["?"] * (len(model)//k)
    for m in model:
        if m > 0:
            assert(cols[(m-1)//k] == "?")
            cols[(m-1)//k] = str((m-1) % k)
    return "".join(cols)

# converts model to exponents (form: k^{n})
def toExponents(model):
    model = [(m-1) % k for m in model if m > 0]
    cols = []
    
    current = model[0]
    count = 1

    for i in range (1, len(model)):
        if model[i] == current:
            count += 1
        else:
            cols.append(str(current) + "^{" + str(count) + "}")
            current = model[i]
            count = 1

    cols.append(str(current) + "^{" + str(count) + "}")
    return " ".join(cols)

# implement exact formulas for families of 3-colour Rado numbers
# Theorem 1.2 from ISAAC paper
def theorems():
    if a == 1 and b == -1 and c >= 1: # eqn: x - y = (m - 2)z
        m = c + 2
        return m**3 - m**2 - m - 1
    elif a == -b and c == a - 1 and a >= 3: # eqn: a(x - y) = (a - 1)z
        return a**3 + (a - 1)**2
    elif a == -b and c >= 1 and a >= c + 2 and math.gcd(a, c) == 1: # eqn: a(x - y) = bz
        return a**3
    else:
        return 0

# check that a theorem can be applied, output results
if theorems():
    f = open(log_name, "w")
    f.write("%d\t%d\t%d\t%d\n" % (a, b, c, theorems()))
    f.close()
    exit(1)

with Cadical153(use_timer = True) as s:
    
    # generate symmetry breaking clauses
    sb_clauses = integer_1_is_colour_1()
    for sb_clause in sb_clauses:
        s.add_clause(sb_clause)

    if b == c:
        nr1 = max(a + 1, b)
    elif a == b and c == 1:
        nr1 = 2*a
    elif a == b:
        nr1 = max(a, math.ceil(b / 2))
    else:
        nr1 = 30 

    # generate fixed colours for variable constraints
    for i in range(n_fixed):
        s.add_clause([mapped_variable(fixed[i], i + 2)])

    while True:

        # generate positive clauses
        s.add_clause(positive_clause(n))

        # generate symmetry breaking clauses
        if n <= nr1:
            s.add_clause(colour_3_cannot_appear_before_colours_1_2(n))

        # list of x, y, z values that satisfy ax + by = cz
        equation_solutions = solve_equation(n)

        # generate negative clauses
        for (x, y, z) in equation_solutions:
            for j in range(1, k + 1):
                s.add_clause(negative_clause(j, x, y, z))

        # generate optional clauses
        for i in range(1, k + 1):
            for j in range(i + 1, k + 1):
                s.add_clause(optional_clause(i, j, n))

        # track results
        if n >= start:
            t = time.time()
            result = s.solve()
            end_time = time.time()

            if result:
                f = open(log_name, "w")
                f.write("S %d\n" % (n))
                f.close()

                number_colouring = toNumbers(s.get_model())
                exponent_colouring = toExponents(s.get_model())
                print("%d %.5f s %.5f s" % (n, end_time-t, end_time-start_time))
            else:
                print("%d %d %d %d" % (a, b, c, n))
                break

        n += 1

# log (n - 1) results
f = open(sat_name, "w")
f.write("S %d\n" % (n - 1))
f.write("Number Colouring: %s\n" % (number_colouring))
f.write("Exponent Colouring: %s\n" % (exponent_colouring))
f.close()

# log (n) results
f = open(log_name, "w")
f.write("%d %d %d\n" % (a, b, c))
f.write("S %d\n" % (start))
f.write("F %d\n" % (n_fixed))

for i in range(n_fixed):
    f.write("%d\n" % (fixed[i]))

f.write("U %d\n" % (n))
f.write("T %.2f\n" % (end_time - start_time))
f.close()

# perform verification on last colouring found
t = time.time()
print("%d %s %s" % (n, number_colouring, check(number_colouring)))
print("Check time: %.2f sec" % (time.time() - t))
print("Solve time: %.2f sec" % (end_time - start_time))
