from collections import defaultdict, Counter

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
            clause = list(map(int, line.strip().split()))[:-1]#Remove the trailing 0's from the end of the lines
            clauses.append(clause)
    return num_variables, clauses

def solve_3sat(file_path):
    num_variables, clauses = parse_dimacs(file_path)

    # Dictionary: variable -> set of clauses containing the variable
    variable_map = defaultdict(set)
    for i, clause in enumerate(clauses):
        for literal in clause:
            variable_map[literal].add(i)

    # Multiset to store satisfied clauses
    satisfied_clauses = Counter()

    # Set of already set variables
    set_variables = {}

    # Sort variables based on how often they appear in clauses (descending order)
    sorted_variables = sorted(variable_map.items(), key=lambda x: len(x[1]), reverse=True)

    def satisfy_clauses(var):
        for clause_index in list(variable_map[var]):
            satisfied_clauses[clause_index] += 1
            if satisfied_clauses[clause_index] == 1:
                for literal in clauses[clause_index]:
                    variable_map[literal].discard(clause_index)

    # Loop to set variables
    for var, _ in sorted_variables:
        if var in set_variables or -var in set_variables:
            continue
        
        pos_size = len(variable_map[var])
        neg_size = len(variable_map[-var])
        
        if pos_size >= neg_size:
            chosen_var = var
        else:
            chosen_var = -var
        
        set_variables[abs(chosen_var)] = (chosen_var > 0)
        satisfy_clauses(chosen_var)

    # If all clauses are satisfied, we're done
    if len(satisfied_clauses) == len(clauses):
        assignment = {var: value for var, value in set_variables.items()}
        return True, assignment, len(clauses)

    # If all variables are assigned but not all clauses satisfied
    satisfied_count = sum(1 for count in satisfied_clauses.values() if count > 0)
    return False, None, satisfied_count

# Example usage:
file_path = r"C:\Users\Vedaang\Desktop\Research\uf20-026.cnf"
result, assignment, satisfied_count = solve_3sat(file_path)

if result:
    print("SATISFIABLE")
    print("Assignment:", assignment)
else:
    print("UNSATISFIABLE")
    print(f"Number of satisfied clauses: {satisfied_count} out of {len(parse_dimacs(file_path)[1])}")
