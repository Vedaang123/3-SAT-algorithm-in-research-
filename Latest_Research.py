from collections import defaultdict, Counter
import time
import random
import os # Import the os module for path manipulation

start = time.time()

def parse_dimacs(file_path):
    """
    Parses a DIMACS CNF file to extract the number of variables and clauses.

    Args:
        file_path (str): The path to the DIMACS CNF file.

    Returns:
        tuple: A tuple containing (num_variables, clauses), where
               num_variables (int): The total number of variables in the problem.
               clauses (list of lists): A list where each inner list represents a clause,
                                       containing integer literals (positive for true, negative for false).
    """
    clauses = []
    num_variables = 0
    try:
        with open(file_path, 'r') as file:
            for line in file:
                line = line.strip()
                if not line or line.startswith('c') or line.startswith('%'):
                    continue
                if line.startswith('p cnf'):
                    parts = line.split()
                    num_variables = int(parts[2])
                    # num_clauses = int(parts[3]) # Number of clauses is inferred from list length
                    continue
                # Clause lines end with '0', so we split and remove the last element
                clause = list(map(int, line.split()))[:-1]
                if clause: # Ensure the clause is not empty after removing '0'
                    clauses.append(clause)
    except FileNotFoundError:
        # print(f"Error: File not found at {file_path}") # Suppress this for automated testing
        return 0, []
    except Exception as e:
        # print(f"Error parsing DIMACS file {file_path}: {e}") # Suppress this for automated testing
        return 0, []
    return num_variables, clauses

def is_clause_satisfied(clause, assignment):
    """
    Checks if a given clause is satisfied by the current variable assignment.

    Args:
        clause (list): A list of literals representing the clause.
        assignment (dict): A dictionary where keys are absolute variable IDs and
                           values are booleans (True for positive, False for negative).

    Returns:
        bool: True if the clause is satisfied, False otherwise.
    """
    for literal in clause:
        var = abs(literal)
        if var in assignment:
            # Check if the literal (positive or negative) evaluates to true
            if (literal > 0 and assignment[var]) or \
               (literal < 0 and not assignment[var]):
                return True
    return False

def count_satisfied_clauses(clauses, assignment):
    """
    Counts the number of clauses satisfied by the current assignment.

    Args:
        clauses (list of lists): All clauses in the SAT problem.
        assignment (dict): Current variable assignment.

    Returns:
        int: The total count of satisfied clauses.
    """
    count = 0
    for clause in clauses:
        if is_clause_satisfied(clause, assignment):
            count += 1
    return count

def get_literal_satisfaction_counts(clauses, assignment):
    """
    Calculates for each clause how many of its literals are true under the current assignment.
    This is crucial for the "multiset" logic to determine if a clause is redundantly satisfied.

    Args:
        clauses (list of lists): All clauses.
        assignment (dict): Current variable assignment.

    Returns:
        Counter: A Counter where keys are clause indices and values are the
                 number of true literals in that clause.
    """
    literal_counts = Counter()
    for i, clause in enumerate(clauses):
        for literal in clause:
            var = abs(literal)
            if var in assignment:
                # If the literal is true under the current assignment
                if (literal > 0 and assignment[var]) or \
                   (literal < 0 and not assignment[var]):
                    literal_counts[i] += 1
    return literal_counts


def solve_3sat(file_path):
    """
    Solves a 3-SAT problem using a two-pass strategy:
    1. A greedy first pass to make initial assignments.
    2. A local search second pass to improve the solution for unsatisfied clauses.

    Args:
        file_path (str): The path to the DIMACS CNF file.

    Returns:
        tuple: (is_satisfiable, assignment, satisfied_count, steps), where
               is_satisfiable (bool): True if a satisfying assignment was found, False otherwise.
               assignment (dict or None): The found assignment {var_id: True/False} if satisfiable, None otherwise.
               satisfied_count (int): The number of clauses satisfied by the final assignment.
               steps (list): A list of tuples detailing the assignment steps taken.
    """
    num_variables, clauses = parse_dimacs(file_path)

    if not clauses:
        # print("No clauses found or error parsing file. Returning.") # Suppress for automated testing
        return False, {}, 0, []

    # --- First Pass: Greedy Heuristic ---
    variable_occurrence_map = defaultdict(set)
    for i, clause in enumerate(clauses):
        for literal in clause:
            variable_occurrence_map[literal].add(i)

    set_variables = {}
    assignment_steps = []

    all_unique_vars = sorted(list(set(abs(l) for clause in clauses for l in clause)))

    sorted_variables_by_occurrence = sorted(all_unique_vars,
                                            key=lambda x: len(variable_occurrence_map[x]) + len(variable_occurrence_map[-x]),
                                            reverse=True)

    for var_abs in sorted_variables_by_occurrence:
        if var_abs in set_variables:
            continue

        pos_size = len(variable_occurrence_map[var_abs])
        neg_size = len(variable_occurrence_map[-var_abs])

        chosen_literal = 0
        reason = ""

        if pos_size >= neg_size:
            chosen_literal = var_abs
            reason = f"Chose {var_abs} (positive) because it appears in {pos_size} clauses vs {-var_abs} in {neg_size} clauses"
        else:
            chosen_literal = -var_abs
            reason = f"Chose {-var_abs} (negative) because it appears in {neg_size} clauses vs {var_abs} in {pos_size} clauses"

        set_variables[var_abs] = (chosen_literal > 0)
        assignment_steps.append((var_abs, chosen_literal > 0, reason))

    best_assignment = {var: val for var, val in set_variables.items()}
    max_satisfied_count = count_satisfied_clauses(clauses, best_assignment)

    # --- Second Pass: Local Search (GSAT-like with user's "multiset" preference) ---
    second_pass_steps = []
    max_flips = num_variables * 5 if num_variables > 0 else 50 # Default to 50 flips if num_variables is 0

    for flip_count in range(max_flips):
        unsatisfied_clause_indices = [i for i, clause in enumerate(clauses)
                                      if not is_clause_satisfied(clause, best_assignment)]

        if not unsatisfied_clause_indices:
            break

        target_clause_idx = random.choice(unsatisfied_clause_indices)
        target_clause = clauses[target_clause_idx]

        best_flip_var_candidate = None
        best_flip_val_candidate = None
        best_candidate_net_gain = -float('inf')
        best_candidate_multiset_cost = float('inf')

        literal_satisfaction_counts = get_literal_satisfaction_counts(clauses, best_assignment)

        for literal_in_clause in target_clause:
            var_to_flip_abs = abs(literal_in_clause)
            hypothetical_val_for_literal = (literal_in_clause > 0)

            temp_assignment = best_assignment.copy()
            temp_assignment[var_to_flip_abs] = hypothetical_val_for_literal

            new_satisfied_count = count_satisfied_clauses(clauses, temp_assignment)
            net_gain = new_satisfied_count - max_satisfied_count

            current_flip_multiset_cost = 0
            original_val_of_var = best_assignment.get(var_to_flip_abs)
            literal_that_was_true_before_flip = None
            if original_val_of_var is not None:
                literal_that_was_true_before_flip = var_to_flip_abs if original_val_of_var else -var_to_flip_abs

            for i, c in enumerate(clauses):
                if is_clause_satisfied(c, best_assignment) and not is_clause_satisfied(c, temp_assignment):
                    if literal_that_was_true_before_flip in c and literal_satisfaction_counts[i] == 1:
                        current_flip_multiset_cost += 1

            if net_gain > best_candidate_net_gain:
                best_candidate_net_gain = net_gain
                best_flip_var_candidate = var_to_flip_abs
                best_flip_val_candidate = hypothetical_val_for_literal
                best_candidate_multiset_cost = current_flip_multiset_cost
            elif net_gain == best_candidate_net_gain:
                if current_flip_multiset_cost < best_candidate_multiset_cost:
                    best_candidate_net_gain = net_gain
                    best_flip_var_candidate = var_to_flip_abs
                    best_flip_val_candidate = hypothetical_val_for_literal
                    best_candidate_multiset_cost = current_flip_multiset_cost

        if best_flip_var_candidate is not None:
            if best_candidate_net_gain > 0 or \
               (best_candidate_net_gain == 0 and not is_clause_satisfied(target_clause, best_assignment) and
                is_clause_satisfied(target_clause, {**best_assignment, best_flip_var_candidate: best_flip_val_candidate})):

                best_assignment[best_flip_var_candidate] = best_flip_val_candidate
                max_satisfied_count = count_satisfied_clauses(clauses, best_assignment)

                second_pass_steps.append((best_flip_var_candidate, best_flip_val_candidate,
                                          f"Flipped {best_flip_var_candidate} to {best_flip_val_candidate} "
                                          f"to target clause {target_clause_idx} (net gain: {best_candidate_net_gain}, "
                                          f"multiset cost: {best_candidate_multiset_cost})"))

    final_satisfied_count = count_satisfied_clauses(clauses, best_assignment)

    if final_satisfied_count == len(clauses):
        return True, best_assignment, len(clauses), assignment_steps + second_pass_steps
    else:
        return False, None, final_satisfied_count, assignment_steps + second_pass_steps

def run_instances(base_path, file_prefix, start_instance, end_instance, num_digits=4):
    """
    Automates testing of 3-SAT instances within a specified range,
    handling filenames with leading zeros.

    Args:
        base_path (str): The base directory where the DIMACS files are located.
        file_prefix (str): The common prefix for the instance filenames (e.g., "uf20-").
        start_instance (int): The starting instance number (inclusive).
        end_instance (int): The ending instance number (inclusive).
        num_digits (int): The number of digits for padding the instance number
                          in the filename (e.g., 4 for '0101').
    """
    print("--- Satisfied Clauses Per Instance ---")
    for i in range(start_instance, end_instance + 1):
        # Format the instance number with leading zeros
        padded_instance_num = f"{i:0{num_digits}d}"
        file_name = f"{file_prefix}{padded_instance_num}.cnf" # Assuming .cnf extension
        full_file_path = os.path.join(base_path, file_name)

        # Call the solver and only extract the satisfied_count
        _, _, satisfied_count, _ = solve_3sat(full_file_path)
        print(satisfied_count)

# === Example Usage ===
# IMPORTANT:
# 1. Replace "Path" with the actual base directory where your DIMACS files are stored.
#    For example, if your files are in 'C:\Users\YourUser\Documents\Research on uf20\uf20-0101.cnf',
#    then base_path should be r"C:\Users\YourUser\Documents\Research on uf20"
# 2. Ensure your files are named consistently, like uf20-0101.cnf, uf20-0102.cnf, etc.

# start_time_overall = time.time() # You can uncomment this to measure overall runtime if needed

base_path = r"C:\Users\Vedaang\Desktop\Research on uf20" # <--- REPLACE THIS WITH YOUR ACTUAL BASE PATH
file_prefix = "uf20-"
start_instance = 1 # Start at 101 if your files are uf20-0101.cnf
end_instance = 9   # End at 101 for a single file test
num_digits_in_filename = 2 # <--- IMPORTANT: Set this to match the number of digits in your filenames (e.g., 4 for '0101')

run_instances(base_path, file_prefix, start_instance, end_instance, num_digits=num_digits_in_filename)

end_time_overall = time.time()
print(f"\nOverall Runtime for instances {start_instance}-{end_instance}: {end_time_overall - start:.2f} seconds")
