def dimacs(clauses, num_literals, num_clauses, outpath):
    with open(outpath, 'w') as f:
        f.write(f'p cnf {num_literals} {num_clauses}\n')
        for clause in clauses:
            f.write(f"{' '.join([str(x) for x in clause])} 0\n")