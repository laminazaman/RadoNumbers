def generate_partition_sets_aaap1(a: int):
    assert a >= 7 and a % 2 == 1, "a must be an odd integer ≥ 7"
    N = a**3 * (a + 1) - 1
    full_range = set(range(1, N + 1))

    S_a, S_a2 = set(), set()
    R_l, B_l, R_r, B_r = set(), set(), set(), set()

    for i in range(a**2):
        for j in range(a + 1):
            base = i * a * (a + 1) + a * j
            if base + a <= N:
                S_a.add(base + a)
                if (i + j + 1) % a == 0:
                    S_a2.add(base + a)
            for k in range(1, a):
                val = base + k
                if val > N:
                    continue
                if k >= 2 * (j // 2) + 1:
                    R_l.add(val)
                else:
                    B_l.add(val)

    # Red R_r
    R_r.add(a**4)
    for i in range(a):
        for j in range(i + 1, a):
            val = i * a**3 + j * a**2
            if val <= N:
                R_r.add(val)
    for i in range(1, (a - 1)//2 + 1):
        val = i * a**3 + i * a**2
        if val <= N:
            R_r.add(val)

    # Blue B_r
    for i in range(1, a):
        val = a**4 + i * a**2
        if val <= N:
            B_r.add(val)
    for i in range(1, a):
        for j in range(i):
            val = i * a**3 + j * a**2
            if val <= N:
                B_r.add(val)
    for i in range((a + 1)//2, a):
        val = i * a**3 + i * a**2
        if val <= N:
            B_r.add(val)

    S_a_diff = S_a - S_a2
    used = S_a_diff | R_l | B_l | R_r | B_r
    unused = full_range - used
    overlap = len(S_a_diff & (R_l | B_l | R_r | B_r)) > 0 or \
              len(R_l & B_l) > 0 or len(R_r & B_r) > 0 or \
              len((R_l | B_l) & (R_r | B_r)) > 0

    return {
        "a": a,
        "Total Expected": N,
        "Size S_a - S_{a^2}": len(S_a_diff),
        "Size R_l": len(R_l),
        "Size B_l": len(B_l),
        "Size R_r": len(R_r),
        "Size B_r": len(B_r),
        "Unused Elements": len(unused),
        "Overlap Detected": overlap,
        "Partition Valid": len(unused) == 0 and not overlap
    }

# Generate LaTeX rows for a = 7 to 29
latex_rows = []
for a in range(7, 30, 2):
    row = generate_partition_sets_aaap1(a)
    latex_rows.append(
        f"{a} & {row['Total Expected']} & {row['Size S_a - S_{a^2}']} & {row['Size R_l']} & "
        f"{row['Size B_l']} & {row['Size R_r']} & {row['Size B_r']} & "
        f"{row['Unused Elements']} & {'Yes' if row['Overlap Detected'] else 'No'} & "
        f"{'Yes' if row['Partition Valid'] else 'No'} \\\\"
        )

# Assemble LaTeX table
latex_table_aaap1 = r"""\begin{table}[h!]
\centering
\begin{tabular}{|c|c|c|c|c|c|c|c|c|c|}
\hline
$a$ & Total & $|S_a \setminus S_{a^2}|$ & $|R_\ell|$ & $|B_\ell|$ & $|R_r|$ & $|B_r|$ & Unused & Overlap & Valid \\
\hline
""" + "\n".join(latex_rows) + r"""
\hline
\end{tabular}
\caption{Partition validation for ${\cal E}(3,0;a,a,a+1)$ from $a=7$ to $29$ (odd)}
\end{table}
"""

print(latex_table_aaap1)
