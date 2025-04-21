# multiple colours, ax + by = cz

import math
import sys
import time

k = 3 # number of colours
n = 1 # counter

result = int(sys.argv[1]) # expected result
clause_count = 0

# equation: ax + by = cz
a = int(sys.argv[2])
b = int(sys.argv[3])
c = int(sys.argv[4])

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
            if y < z:
                solutions.add((y, z, n))
            else:
                solutions.add((z, y, n))

    if a != b:
        y = n
        sols = diophantine_solutions(-a, c, b*n)
        for sol in sols:
            x = sol[0]
            z = sol[1]
            if a*x + b*y == c*z and 1 <= x and x <= n and 1 <= z and z <= n:
                if x < z:
                    solutions.add((x, z, n))
                else:
                    solutions.add((z, x, n))

    z = n
    sols = diophantine_solutions(a, b, c*n)
    for sol in sols:
        x = sol[0]
        y = sol[1]
        if a*x + b*y == c*z and 1 <= x and x <= n and 1 <= y and y <= n:
            if x < y:
                solutions.add((x, y, n))
            else:
                solutions.add((y, x, n))

    return solutions

def write_clause(clause, file):
    file.write(" ".join(map(str, clause)) + " 0\n")

cnf_file = open(f"logs/cnf_files/clauses_{result}_{a}.{b}.{c}.cnf", "w")

if result == 0:
    cnf_file.write("p cnf 0 0\n")
    cnf_file.close()
    exit()

# count clauses
while n <= result:

    clause_count += 1 # positive clauses
    clause_count += (k * (k - 1) // 2) # optional clauses

    # negative clauses
    equation_solutions = solve_equation(n)
    for i in range(len(equation_solutions)):
        clause_count += k

    n += 1

# start timer
start_time = time.time()

# generate symmetry breaking clauses
sb_clauses = integer_1_is_colour_1()

n = 1
while solve_equation(n) == [] and n < result:
    n += 1
    sb_clauses += [colour_3_cannot_appear_before_colours_1_2(n)]
    
clause_count += len(sb_clauses)

cnf_file.write("p cnf %d %d\n" % (result * 3, clause_count))

for sb_clause in sb_clauses:
    write_clause(sb_clause, cnf_file)

n = 1

while True:

    # generate positive clauses
    write_clause(positive_clause(n), cnf_file)

    # list of x, y, z values that satisfy ax + by = cz
    equation_solutions = solve_equation(n)

    # generate negative clauses
    for (x, y, z) in equation_solutions:
        for j in range(1, k + 1):
            write_clause(negative_clause(j, x, y, z), cnf_file)

    # generate optional clauses
    for i in range(1, k + 1):
        for j in range(i + 1, k + 1):
            write_clause(optional_clause(i, j, n), cnf_file)

    # print results
    if n == result:
        print("%d %d %d %d" % (a, b, c, n))
        break
    else:
        print("%d" % (n))

    n += 1

cnf_file.close()

# end timer
end_time = time.time()

time_file = open(f"logs/generation_time/time_{result}_{a}.{b}.{c}.txt", "w")
time_file.write("%.2f\n" % (end_time - start_time))
time_file.close()
