from sympy import symbols, Eq, pretty
import sys
import json


class CSP_generic:
    def __init__(self, problem):
        self.variables, self.domains, self.constraints = problem
        self.expanded_nodes = 0

    def backtracking_search(self):
        return self._recursive_backtracking({})

    def _recursive_backtracking(self, assignment):
        self.expanded_nodes += 1
        if self._is_complete(assignment):
            return assignment
        # Select a variable
        var = self._select_unassigned_variable(assignment)
        if var is None:
            return False
        # Now select a value
        for value in self._order_domain_value(var, assignment):
            # If consistent continue searching
            if self._is_consistent(assignment, var, value):
                assignment[var] = value
                if self._constraint_propagation(assignment):
                    result = self._recursive_backtracking(assignment)
                    if result is not False:
                        return result
                del assignment[var]
        return False

    def _is_complete(self, assignment):
        # All variables assigned correctly
        return all(var in assignment for var in self.variables)

    def _select_unassigned_variable(self, assignment):
        # Implement selection method (selection of the first element may be changes) (MRV, degree heuristic)
        unassigned_variables = [
            var for var in self.variables if var not in assignment]
        mrv_variable = self._minimum_remaining_variables(unassigned_variables)
        candidates = [var for var in mrv_variable if len(self.domains[var]) == len(self.domains[mrv_variable[0]])]
        if len(candidates) > 1:
            return self._degree_heuristic(unassigned_variables)
        return candidates[0]

    def _order_domain_value(self, variable, assignment):
        # Implement ordering method (LCV)
        return self._least_constrained_value(variable, assignment)

    def _is_consistent(self, assignment, variable, value):
        # Assign the selected value to the given variable
        temp_assignment = {**assignment, variable: value}
        constraint_checks_queen = {
            "row-different": lambda v1, v2: v1[0] != v2[0],
            "column-different": lambda v1, v2: v1[1] != v2[1],
            "diagonal-different": lambda v1, v2: abs(v1[0] - v2[0]) != abs(v1[1] - v2[1])
        }
        for constraint in self.constraints:
            if "variable1" in constraint and "variable2" in constraint:
                var1, var2 = constraint["variable1"], constraint["variable2"]
                if variable in (var1, var2):
                    # Identify the neighbour variable
                    other_var = var2 if var1 == variable else var1
                    # Check the assignment of the neigbour variable and whether it conflicts or not
                    if other_var in temp_assignment:
                        val1, val2 = temp_assignment[var1], temp_assignment[other_var]
                        if "Q[" in self.variables:
                            if not constraint_checks_queen[constraint["type"]](val1, val2):
                                return False
                        elif "WA" in self.variables:
                            if val1 == val2:
                                return False
                        elif "F" in self.variables:
                            try:
                                if "expression" in constraint:
                                    if all(eval(constraint["expression"], {}, temp_assignment)):
                                        return True
                            except:
                                pass
                        else:
                            raise ValueError("Problem type is not defined.")
            elif "variables" in constraint and variable in constraint["variables"]:
                if "type" in constraint and constraint["type"] == "different":
                    for other_var in constraint["variables"]:
                        if other_var != variable and other_var in temp_assignment:
                            if temp_assignment[variable] == temp_assignment[other_var]:
                                return False
                elif "expression" in constraint:
                    try:
                        if not eval(constraint["expression"], {}, temp_assignment):
                            return False
                    except:
                        return False
        return True

    def _minimum_remaining_variables(self, unassigned_var):
        # MRV to be used in selection of the variables, we will take the minimum
        return sorted(unassigned_var, key=lambda var: len(self.domains[var]))
    
    def _degree_heuristic(self, unassigned_var):
        # Tie breaker of MRV
        return max(unassigned_var, key=lambda var: len(self._neighbours(var)))

    def _count_conflict(self, variable, value, assignment):
        # Used in LCV to order the consistent values of neighboring variables from highest to lowest
        conflict_count = 0
        for constraint in self.constraints:
            if variable in constraint:
                other_var = constraint[1] if constraint[0] == variable else constraint[0]
                if other_var not in assignment:
                    for other_value in self.domains[other_var]:
                        # Check if it affects a value that is a constraint
                        if not self._is_consistent({variable: value, other_var: other_value}, variable, value):
                            conflict_count += 1
        return conflict_count

    def _least_constrained_value(self, variable, assignment):
        return sorted(
            self.domains[variable],
            key=lambda value: self._count_conflict(variable, value, assignment)
        )

    def _constraint_propagation(self, assignment):
        # Arc consistency
        queue = [(var1, var2) for var1 in self.variables for var2 in self._neighbours(var1)]
        # Reduce values that causes conflict as much as possible
        while queue:
            # Pop a set of variables that has a constraint
            (var1, var2) = queue.pop(0)
            if self._remove_value(var1, var2):
                if not self.domains[var1]:
                    return False
                for neighbour in self._neighbours(var1):
                    if neighbour != var2 and neighbour not in assignment:
                        # For consistency add the removed neighbours
                        queue.append((neighbour, var1))
        return True
    
    def _remove_value(self, var1, var2):
        removed = False
        for val in self.domains[var1]:
            if not any(self._is_consistent({var1: val, var2: val2}, var1, val) for val2 in self.domains[var2]):
                self.domains[var1].remove(val)
                removed = True
        return removed

    def _neighbours(self, variable):
        # Return all variables that has conflicts with the given variable
        neighbours = set()
        for constraint in self.constraints:
            if "variable1" in constraint and "variable2" in constraint:
                var1, var2 = constraint["variable1"], constraint["variable2"]
                if variable == var1 and var2 not in neighbours:
                        neighbours.add(var2)
                elif variable == var2 and var1 not in neighbours:
                    neighbours.add(var1)
            elif "variables" in constraint and variable in constraint["variables"]:
                for var in constraint["variables"]:
                    if var != variable:
                        neighbours.add(var)
            
        # Return all variables that has conflicts with the given variable
        return neighbours


def n_queens_problem(n):
    variables = [f"Q[{i+1}]" for i in range(n)]
    domains = {q: [(row, column) for row in range(n)
                   for column in range(n)] for q in variables}
    constraints = []
    for i in range(n):
        for j in range(i+1, n):
            constraints.append(
                {"type": "row-different", "variable1": f"Q{i+1}", "variable2": f"Q{j+1}"})
            constraints.append(
                {"type": "column-different", "variable1": f"Q{i+1}", "variable2": f"Q{j+1}"})
            constraints.append(
                {"type": "diagonal-different", "variable1": f"Q{i+1}", "variable2": f"Q{j+1}"})

    return variables, domains, constraints


def map_coloring_problem(n):
    variables = ["WA", "NT", "Q", "NSW", "V", "SA", "T"]
    domains = {region: [f"c{i+1}" for i in range(n)] for region in variables}
    constraints = [{f"type": "color-different", "variable1": {var1}, "variable2": {var2}}
                   for var1 in variables for var2 in variables if var1 != var2]

    return variables, domains, constraints


def cryptarithmethic_problem(n):
    carry_variables = [f"x{i+1}" for i in range(1, n+2)]
    if n == 0:
        variables = ["F", "R", "O", "T"]
        constraints = [{"type": "sum", "expression": "O + O == R + 10 * x1"},
                       {"type": "sum", "expression": "T + T + x1 == O + 10 * x2"},
                       {"type": "sum", "expression": "F == x2"},
                       {"type": "different", "variables": variables + carry_variables}]
    elif n == 1:
        variables = ["F", "R", "O", "T", "W"]
        constraints = [{"type": "sum", "expression": "O + O == R + 10 * x1"},
                       {"type": "sum", "expression": "W + W + x1 == W + 10 * x2"},
                       {"type": "sum", "expression": "T + T + x2 == O + 10 * x3"},
                       {"type": "sum", "expression": "F == x3"},
                       {"type": "different", "variables": variables + carry_variables}]
    elif n == 2:
        variables = ["F", "R", "O", "T", "W", "X"]
        constraints = [{"type": "sum", "expression": "O + O == R + 10 * x1"},
                       {"type": "sum", "expression": "W + W + x1 == X + 10 * x2"},
                       {"type": "sum", "expression": "X + X + x2 == W + 10 * x3"},
                       {"type": "sum", "expression": "T + T + x3 == O + 10 * x4"},
                       {"type": "sum", "expression": "F == x4"},
                       {"type": "different", "variables": variables + carry_variables}]
    elif n == 3:
        variables = ["F", "R", "O", "T", "W", "X", "Y"]
        constraints = [{"type": "sum", "expression": "O + O == R + 10 * x1"},
                       {"type": "sum", "expression": "W + W + x1 == Y + 10 * x2"},
                       {"type": "sum", "expression": "X + X + x2 == X + 10 * x3"},
                       {"type": "sum", "expression": "Y + Y + x3 == W + 10 * x4"},
                       {"type": "sum", "expression": "T + T + x4 == O + 10 * x5"},
                       {"type": "sum", "expression": "F == x5"},
                       {"type": "different", "variables": variables + carry_variables}]
    else:
        raise ValueError("n is not defined.")

    domains = {letter: list(range(10)) if letter != "T" else list(
        range(1, 10)) for letter in variables}
    domains.update({x: [0, 1] for x in carry_variables})

    return variables + carry_variables, domains, constraints


def create_problem(type, n):
    if type == "P1":
        return n_queens_problem(n)
    elif type == "P2":
        return map_coloring_problem(n)
    elif type == "P3":
        return cryptarithmethic_problem(n)
    else:
        raise ValueError("Problem type is not defined.")


def save_problem(problem, file_name):
    variables, domains, constraints = problem
    problem_dict = {
        "Variables": variables,
        "Domains": domains,
        "Constraints": []
    }
    if "F" in variables:
        for constraint in constraints:
            if constraint['type'] == 'sum':
                problem_dict['Constraints'].append({
                    'type': 'sum',
                    'expression': constraint['expression']
                })
            elif constraint['type'] == 'different':
                problem_dict['Constraints'].append({
                    'type': 'different',
                    'variables': constraint['variables']
                })
    else:
        for constraint in constraints:
            constraint_dict = {
                'type': constraint['type'],
                'variable1': list(constraint['variable1']),
                'variable2': list(constraint['variable2'])
            }
            problem_dict['Constraints'].append(constraint_dict)
        
    with open(file_name, "w") as file:
        # data interchange and storage, readable, compatible, and easy to use across different platforms and languages
        json.dump(problem_dict, file, separators=(",", ":"))


def load_problem(file_name):
    with open(file_name, "r") as file:
        problem = json.load(file)
    return problem["Variables"], problem["Domains"], problem["Constraints"]


if __name__ == "__main__":
    args = sys.argv[1:]  # get everything after the script name
    problem = None

    if len(args) == 3:
        # Return the problem details
        n, problem_type, file_name = int(args[0]), args[1], args[2]

        problem = create_problem(problem_type, n)

        save_problem(problem, file_name)

        print("Problem is saved.")

    elif len(args) == 5:
        # Return the solution
        heuristics, file_name = args[:-1], args[-1]
        try:
            problem = load_problem(file_name)
            csp = CSP_generic(problem)
            solution = csp.backtracking_search()
            with open(file_name, "w") as file:
                if solution is not False:
                    for var, val in solution.items():
                        file.write(f"{var}: {val}\n")
                    file.write(
                        f"Number of expanded nodes: {csp.expanded_nodes}\n")
                    print("Solution is saved.")
                else:
                    file.write(
                        f"Number of expanded nodes: {csp.expanded_nodes}\nNo solution.")
                    print("No solution.")
        except Exception as e:
            raise ValueError(
                "Problem type and size not provided from the first command.") from e
