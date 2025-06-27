from collections import defaultdict, Counter
import time

start = time.time()

def parse_dimacs(file_path):
    clauses = []
    with open(file_path, 'r') as file:
        for line in file:
            if line.startswith('c') or line.startswith('%') or line.startswith('0') or line.strip() == '':
                continue
            if line.startswith('p'):
                parts = line.strip().split()
                num_variables = int(parts[2])
                num_clauses = int(parts[3])
                continue
            clause = list(map(int, line.strip().split()))[:-1]
            clauses.append(clause)
    return num_variables, clauses

def solve_3sat(file_path):
    num_variables, clauses = parse_dimacs(file_path)

    variable_map = defaultdict(set)
    for i, clause in enumerate(clauses):
        for literal in clause:
            variable_map[literal].add(i)

    satisfied_clauses = Counter()
    set_variables = {}
    assignment_steps = []

    sorted_variables = sorted(variable_map.items(), key=lambda x: len(x[1]), reverse=True)

    def satisfy_clauses(var):
        for clause_index in list(variable_map[var]):
            satisfied_clauses[clause_index] += 1
            if satisfied_clauses[clause_index] == 1:
                for literal in clauses[clause_index]:
                    variable_map[literal].discard(clause_index)

    for var, _ in sorted_variables:
        if var in set_variables or -var in set_variables:
            continue
        
        pos_size = len(variable_map[var])
        neg_size = len(variable_map[-var])

        if pos_size >= neg_size:
            chosen_var = var
            reason = f"Chose {var} (positive) because it appears in {pos_size} clauses vs {-var} in {neg_size} clauses"
        else:
            chosen_var = -var
            reason = f"Chose {-var} (negative) because it appears in {neg_size} clauses vs {var} in {pos_size} clauses"
        
        set_variables[abs(chosen_var)] = (chosen_var > 0)
        assignment_steps.append((abs(chosen_var), chosen_var > 0, reason))
        satisfy_clauses(chosen_var)

    if len(satisfied_clauses) == len(clauses):
        assignment = {var: value for var, value in set_variables.items()}
        return True, assignment, len(clauses), assignment_steps

    satisfied_count = sum(1 for count in satisfied_clauses.values() if count > 0)
    return False, None, satisfied_count, assignment_steps

# === Example Usage ===
file_path = r"C:\Users\Vedaang\Desktop\Research on uf20\industry-2.cnf"  # Replace with actual path
result, assignment, satisfied_count, steps = solve_3sat(file_path)

end = time.time()

print("\n--- Variable Assignment Steps ---")
for var, val, reason in steps:
    print(f"Variable {var} set to {val} → {reason}")

print("\n--- Final Result ---")
if result:
    print("SATISFIABLE")
    print("Assignment:", assignment)
else:
    print("UNSATISFIABLE")
    print(f"Number of satisfied clauses: {satisfied_count} out of {len(parse_dimacs(file_path)[1])}")

print(f"Runtime: {end - start:.2f} seconds")
