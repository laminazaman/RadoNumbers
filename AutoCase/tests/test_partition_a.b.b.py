from math import gcd

def generate_partition_sets_abb(a: int, b: int):
    assert a > b >= 3 and gcd(a, b) == 1 and a**2 + a + b > b**2 + a * b, "Assumptions not satisfied"
    upper = a**3 + a**2 + (2 * b + 1) * a
    full_range = set(range(1, upper + 1))

    # Partition intervals
    P0 = set(range(1, b * a + 1))
    P1 = set(range(b * a + 1, b**2 * a + 1))
    P2 = set(range(b**2 * a + 1, b * a**2 + b * a + 1))
    P3 = set(range(b * a**2 + b * a + 1, a**3 + a**2 + (b + 1) * a + 1))
    P4 = set(range(a**3 + a**2 + (b + 1) * a + 1, upper + 1))

    R1 = {v for v in P0 if v % b != 0}
    R2 = {v for v in (P0 | P1) if v % (b**2) == 0}
    R3 = set(P4)

    B1 = {v for v in (P0 | P1) if v % b == 0 and v % (b**2) != 0}
    B2 = {v for v in P2 if v % b == 0}

    D1 = {v for v in (P1 | P2) if v % b != 0}
    D2 = set(P3)

    red = R1 | R2 | R3
    blue = B1 | B2
    dark = D1 | D2

    used = red | blue | dark
    unused = full_range - used
    overlap = len(red & blue) > 0 or len(red & dark) > 0 or len(blue & dark) > 0

    return {
        "a": a,
        "b": b,
        "Total Expected": upper,
        "Size Red": len(red),
        "Size Blue": len(blue),
        "Size Dark": len(dark),
        "Unused Elements": len(unused),
        "Overlap Detected": overlap,
        "Partition Valid": len(unused) == 0 and not overlap
    }

# Generate table for all valid (a, b)
valid_abb_rows = []
for a in range(4, 30):
    for b in range(3, a):
        if gcd(a, b) == 1 and (a**2 + a + b > b**2 + b * a):
            r = generate_partition_sets_abb(a, b)
            valid_abb_rows.append(
                f"{r['a']} & {r['b']} & {r['Total Expected']} & {r['Size Red']} & {r['Size Blue']} & "
                f"{r['Size Dark']} & {r['Unused Elements']} & {'Yes' if r['Overlap Detected'] else 'No'} & "
                f"{'Yes' if r['Partition Valid'] else 'No'} \\\\"
            )

# Output LaTeX code
latex_code = r"""\begin{table}[h!]
\centering
\begin{tabular}{|c|c|c|c|c|c|c|c|c|}
\hline
$a$ & $b$ & Total & $|\text{Red}|$ & $|\text{Blue}|$ & $|\text{Dark}|$ & Unused & Overlap & Valid \\
\hline
""" + "\n".join(valid_abb_rows) + r"""
\hline
\end{tabular}
\caption{Partition validation for ${\cal E}(3,0;a,b,b)$ with all valid $(a,b)$ pairs where $4 \leq a < 30$, $b \geq 3$, $a > b$, $\gcd(a,b)=1$, and $a^2+a+b > b^2+ba$}
\end{table}
"""

print(latex_code)
