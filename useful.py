from sage.all import *
from itertools import combinations
from string import ascii_lowercase
from itertools import product

def random_problem(random_seed = None, rows = 4, cols = 5):
    """Creates random matrix with given dimensions using given random seed."""
    
    from sage.matrix.constructor import random_echelonizable_matrix
    matrix_space = sage.matrix.matrix_space.MatrixSpace(QQ, rows, cols)
    if random_seed is not None:
        set_random_seed(random_seed)
    A = random_echelonizable_matrix(matrix_space, rank=min(rows, cols), upper_bound=40)
    b = random_vector(QQ, rows)
    c = random_vector(QQ, cols)
    
    P = InteractiveLPProblemStandardForm(A, b, c)
    
    return P

##########################################################################################################

def klee_minty_problem(size = 3):
    """Creates Klee-Minty problem with given size."""

    # Creating a list of lists - A elements
    L = []
    for row in range(size):
        l = []
        for col in range(size):
            if row == col:
                l.append(1)
            elif row <= col:
                l.append(0)
            else:
                l.append(2**(row + 1 - col))
        L.append(l)
        
    A = matrix(QQ, L)            
    b = vector(QQ, [5**(i) for i in range(1,size+1)])
    c = vector(QQ, [2**(size-i) for i in range(1, size+1)])
    P = InteractiveLPProblemStandardForm(A, b, c)
    
    return P

##########################################################################################################

def basic_solutions(P: InteractiveLPProblemStandardForm):
    """Computes dictionary of basic feasible solutions of P indexed by basic sets, i.e. a mapping <basic set> -> <basic solution>."""
    
    A = P.A()
    n = A.ncols() # number of variables
    m = A.nrows() # number of constraints
    A = A.augment(identity_matrix(m))
    S = dict()
    
    b = P.b()
    for BasicSet in combinations(range(n + m), m):
        AB = A.matrix_from_columns(BasicSet)
        if AB.det() != 0:
            # We have found a basic set
            x = AB.inverse() * b
            
            if min(x) >= 0:
                # We have found a feasible basic solution
                S[BasicSet] = vector(QQ, [x[BasicSet.index(i)] if i in BasicSet else 0 for i in range(n+m)])
    return S

########################################################################################################

def solution_graph(P: InteractiveLPProblemStandardForm):
    """
    Create a graph (V, E) where
    V = set of basic feasible sets of P (vertices of the solution graph),
    E = pairs (B1, B2) of basic feasible sets of P such that #(B1 / B2) = 1 and #(B2 / B1) = 1.
    The edges are oriented in the direction of the gradient of the objective function."""
    
    c = vector(QQ, P.c().list() + ([0] * P.A().nrows()))
    
    S = basic_solutions(P)
    V = set(S)
    E = list()
    for B1 in V:
        for B2 in V:
            S1 = set(B1)
            S2 = set(B2)
            if len(S1.difference(S2)) == 1 and len(S2.difference(S1)) == 1:
                if c * S[B1] <= c * S[B2]:
                    E.append((B1, B2, c * S[B2] - c * S[B1]))
   
    g = DiGraph(E)
    return g

######################################################################################################

def labelled_solution_graph(P: InteractiveLPProblemStandardForm):
    c = vector(QQ, P.c().list() + ([0] * P.A().nrows()))

    vname = []
    for length in range(1, 3):
        for combo in product(ascii_lowercase, repeat=length):
            vname.append(''.join(combo))
    
    names = {}
    
    S = basic_solutions(P)
    E = list()
    for n1, B1 in enumerate(S):
        names[B1] = vname[n1]
        
        for n2, B2 in enumerate(S):
            S1 = set(B1)
            S2 = set(B2)
            if len(S1.difference(S2)) == 1 and len(S2.difference(S1)) == 1:
                if c * S[B1] <= c * S[B2]:
                    E.append((vname[n1], vname[n2], c * S[B2] - c * S[B1]))
   
    g = DiGraph(E)
    return g, names

###################################################################################################

def bland_rule(P, G, r_name, v, verb=False):
    """
    P - problem
    G - labelled graph
    r_name - reverse mapping vertex label -> base (enumerated from 1 to n)
    v - vertex label
    
    Returns vertex w such that Bland's rule will pivot from v to w.
    
    Returns None if there is no pivot (either v is optimal or problem is unbounded).
    """
        
    if verb:
        print(f'Wierzchołek {v}, zmienne bazowe {r_name[v]}')
        print(f'Sąsiedzi (krawędzie wychodzące): {G.neighbors_out(v)}')
    
    min_out = min_in = P.A().ncols() + P.A().nrows() + 1
    min_w = None
    
    for w in G.neighbors_out(v):
        (x_in,) = set(r_name[w]) - set(r_name[v])
        (x_out,) = set(r_name[v]) - set(r_name[w])

        if verb:
            print(f'Dla sąsiada {w} zmienna wchodząca to x{x_in} i wychodząca to x{x_out}.')
        
        if x_in < min_in or (x_in == min_in and x_out < min_out):
            min_in = x_in
            min_out = x_out
            min_w = w           
    
    if verb:
        print(f'Wybieram zmienną wchodzącą x{min_in}, wychodzącą x{min_out} i przejście do wierzchołka {min_w}.')
    
    return min_w

########################################################################################################

def largest_coefficient_rule(P, G, r_name, v, verb=False):
    """
    P - problem
    G - labelled graph
    r_name - reverse mapping vertex label -> base (enumerated from 1 to n)
    v - vertex label
    
    Returns vertex w such that largest coefficient rule will pivot from v to w.
    
    Returns None if there is no pivot (either v is optimal or problem is unbounded).
    """ 
    
    if verb:
        print(f'Wierzchołek {v}, zmienne bazowe {r_name[v]}')
        print(f'Sąsiedzi (krawędzie wychodzące): {G.neighbors_out(v)}')
        
    D = P.dictionary(*r_name[v])
    t = list(zip(D.objective_coefficients(),D.nonbasic_variables()))
    # Function which converts variable's name into its index. For example 'x4' -> 4
    def conv1(t):
        T = list()
        for item in t:
            T.append((item[0],int(str(item[1])[1])))
        return T
        
    result = conv1(t)
    
    coeff_max = 0
    for (coeff, var) in result:
        if coeff > 0 and coeff_max < coeff:
            coeff_max = coeff
            var_coeff_max = var
    if coeff_max > 0:
        x_final_in = var_coeff_max
    else:
        return None
    x_final_out = None    
    output_w = None    

    for w in G.neighbors_out(v):
        (x_in,) = set(r_name[w]) - set(r_name[v])
        (x_out,) = set(r_name[v]) - set(r_name[w])
        
        if verb:
            print(f'Dla sąsiada {w} zmienna wchodząca to x{x_in} i wychodząca to x{x_out}.')
        if x_final_in == x_in:
            x_final_out = x_out
            output_w = w
    if x_final_out == None:
        if verb:
            print("Brak przejścia")
        return None
    if verb:
        print(f'Wybieram zmienną wchodzącą x{x_final_in}, wychodzącą x{x_final_out} i przejście do wierzchołka {output_w}.')
        
    return output_w

#########################################################################################################

def largest_increase_rule(P, G, r_name, v, verb=False):
    """
    P - problem
    G - labelled graph
    r_name - reverse mapping vertex label -> base (enumerated from 1 to n)
    v - vertex label
    
    Returns vertex w such that largest increase rule will pivot from v to w.
    
    Returns None if there is no pivot (either v is optimal or problem is unbounded).
    """ 
    
    if verb:
        print(f'Wierzchołek {v}, zmienne bazowe {r_name[v]}')
        print(f'Sąsiedzi (krawędzie wychodzące): {G.neighbors_out(v)}')
        
    D = P.dictionary(*r_name[v])
    max_obj_val = D.objective_value()
    
    output_w = None
    
    for w in G.neighbors_out(v):
        (x_in,) = set(r_name[w]) - set(r_name[v])
        (x_out,) = set(r_name[v]) - set(r_name[w])

        if verb:
            print(f'Dla sąsiada {w} zmienna wchodząca to x{x_in} i wychodząca to x{x_out}.')
        
        K = P.dictionary(*r_name[w])
        obj_val_w = K.objective_value()
        
        if obj_val_w > max_obj_val:
            max_obj_val = obj_val_w
            x_final_in = x_in
            x_final_out = x_out
            output_w = w
    if verb:
        print(f'Wybieram zmienną wchodzącą x{x_final_in}, wychodzącą x{x_final_out} i przejście do wierzchołka {output_w}.')
        
    return output_w

########################################################################################################

def steepest_edge_rule(P, G, r_name, v, verb=False):
    """
    P - problem
    G - labelled graph
    r_name - reverse mapping vertex label -> base (enumerated from 1 to n)
    v - vertex label
    
    Returns vertex w such that steepest edge rule will pivot from v to w.
    
    Returns None if there is no pivot (either v is optimal or problem is unbounded).
    """ 
    import numpy as np
    
    if verb:
        print(f'Wierzchołek {v}, zmienne bazowe {r_name[v]}')
        print(f'Sąsiedzi (krawędzie wychodzące): {G.neighbors_out(v)}')
        
    D = P.dictionary(*r_name[v])
    t = list(zip(D.objective_coefficients(),D.nonbasic_variables()))
    # Function which converts list of tuples in a way that variable's name changes into its index. For example 'x4' -> 4
    def conv1(list_of_tuples):
        T = list()
        for tuple_ in list_of_tuples:
            T.append((tuple_[0],int(str(tuple_[1])[1])))
        return T
    converted_nonbasic = conv1(t)
    Obj_fun = [0]*(len(D.basic_variables())+len(D.nonbasic_variables()))
    for item in converted_nonbasic:
        Obj_fun[item[1]-1] = item[0] 
        
    r = list(zip(D.constant_terms(),D.basic_variables()))
    converted_basic = conv1(r)
    Basic_sol_v = [0]*(len(D.basic_variables())+len(D.nonbasic_variables()))
    for item in converted_basic:
        Basic_sol_v[item[1]-1] = item[0]
            
    output_w = None 
    Formula_max = -10000 # setting Formula_max as -10000 for convinience
    for w in G.neighbors_out(v):
        (x_in,) = set(r_name[w]) - set(r_name[v])
        (x_out,) = set(r_name[v]) - set(r_name[w])

        if verb:
            print(f'Dla sąsiada {w} zmienna wchodząca to x{x_in} i wychodząca to x{x_out}.')
        
        K = P.dictionary(*r_name[w])
        Basic_sol_w = [0]*len(Basic_sol_v)
        for item in conv1(list(zip(K.constant_terms(),K.basic_variables()))):
            Basic_sol_w[item[1]-1] = item[0]

        Basic_sol_diff = []
        for i in range(len(Basic_sol_v)):
            Basic_sol_diff.append(Basic_sol_w[i] - Basic_sol_v[i])

        Formula = np.array(Obj_fun).dot(np.array(Basic_sol_diff))/np.linalg.norm(Basic_sol_diff)

        if Formula > Formula_max:
            Formula_max = Formula
            x_final_in = x_in
            x_final_out = x_out
            output_w = w
    if verb:
        print(f'Wybieram zmienną wchodzącą x{x_final_in}, wychodzącą x{x_final_out} i przejście do wierzchołka {output_w}.')
        
    return output_w

#########################################################################################################

def own_rule(P, G, r_name, v, verb=False):
    """
    P - problem
    G - labelled graph
    r_name - reverse mapping vertex label -> base (enumerated from 1 to n)
    v - vertex label
    
    Returns vertex w such that "lowest positive coefficient rule" will pivot from v to w.
    
    Returns None if there is no pivot (either v is optimal or problem is unbounded).
    """ 
    
    if verb:
        print(f'Wierzchołek {v}, zmienne bazowe {r_name[v]}')
        print(f'Sąsiedzi (krawędzie wychodzące): {G.neighbors_out(v)}')
        
    D = P.dictionary(*r_name[v])
    t = list(zip(D.objective_coefficients(),D.nonbasic_variables()))
    # Function which converts variable's name into its index. For example 'x4' -> 4
    def conv1(t):
        T = list()
        for item in t:
            T.append((item[0],int(str(item[1])[1])))
        return T
        
    result = conv1(t)
    L = [(coeff, var) for (coeff,var) in result if coeff > 0] # list of coefficients greater than 0
    if len(L) > 0:
        for (coeff, var) in L:
            if coeff == min([coeff for (coeff, var) in L]):
                coeff_min = coeff
                var_coeff_min = var
    else:
        return None
    x_final_out = None    
    output_w = None    
    x_final_in = var_coeff_min
    
    for w in G.neighbors_out(v):
        (x_in,) = set(r_name[w]) - set(r_name[v])
        (x_out,) = set(r_name[v]) - set(r_name[w])

        if verb:
            print(f'Dla sąsiada {w} zmienna wchodząca to x{x_in} i wychodząca to x{x_out}.')
        if x_final_in == x_in:
            x_final_out = x_out
            output_w = w
    if x_final_out == None:
        if verb:
            print("Brak przejścia")
        return None
    if verb:
        print(f'Wybieram zmienną wchodzącą x{x_final_in}, wychodzącą x{x_final_out} i przejście do wierzchołka {output_w}.')
        
    return output_w

########################################################################################################

def is_set_of_feasible_solution_bounded(P: InteractiveLPProblemStandardForm):
    '''
        if optimal solution exists for every vector from standard basis then the set of feasible solutions is bounded
    '''
    import numpy as np
    A = P.A()
    b = P.b()
    c_= np.zeros(np.array(A).shape[1])
    unlimited = False
    for i in range(len(c_)): # tworzymy problem i sprawdzamy wartość optymalną
        c = np.zeros(np.array(A).shape[1])
        c[i] = 1
        c = vector(QQ, c)
        P = InteractiveLPProblemStandardForm(A,b,c)
        if P.optimal_value()== None:
            unlimited = True
            break
    if unlimited == True:
        print('Zbiór rozwiązań dopuszczalnych jest nieograniczony')
    else: 
        print('Zbiór rozwiązań dopuszczalnych jest ograniczony')

############################################################################################################

def generate_edges(P, G, r_name):
    bland_edges = []
    l_coeff_edges = []
    l_increase_edges = []
    steepest_edges = []
    own_rule_edges = []
    
    for v in G:
        w = bland_rule(P, G, r_name, v)
        if w is not None:
            bland_edges.append((v, w))
        
        w = largest_coefficient_rule(P, G, r_name, v)
        if w is not None:
            l_coeff_edges.append((v, w))

        w = largest_increase_rule(P, G, r_name, v)
        if w is not None:
            l_increase_edges.append((v, w))

        w = steepest_edge_rule(P, G, r_name, v)
        if w is not None:
            steepest_edges.append((v, w))

        w = own_rule(P, G, r_name, v)
        if w is not None:
            own_rule_edges.append((v, w))
            
    return bland_edges, l_coeff_edges, l_increase_edges, steepest_edges, own_rule_edges

####################################################################################################

def print_table(P, G, r_name):
    import pandas as pd
    from IPython.display import display, HTML
    
    bland_edges, l_coeff_edges, l_increase_edges, steepest_edges, own_rule_edges = generate_edges(P, G, r_name)
    list_of_lists_of_edges = [bland_edges, l_coeff_edges, l_increase_edges, steepest_edges, own_rule_edges]
    sink = G.sinks()
    optimal_vertex = sink[0]
    
    dct = dict(zip(r_name.keys(), [[item] for item in r_name.keys()]))
    srednia = []
    maksymalna = []
    for i in range(5):
        H = G.subgraph(G.vertices(), list_of_lists_of_edges[i])
        dct[str(optimal_vertex)].append(0)
        s = 0
        m = 0
        l = 0
        for path in H.all_paths_iterator(ending_vertices=[str(optimal_vertex)]):
            dct[str(path[0])].append(len(path))
            s += len(path)
            if len(path) > m:
                m = len(path)
            l += 1
        if l !=0:
            srednia.append("{:.2f}".format(float(s/l)))
        else:
            srednia.append("error")
        maksymalna.append(m)    

    columns = ["Vertex", "Bland rule", "Largest coefficient rule", "Largest increase rule", "Steepest edge", "Own rule"]
    DF = pd.DataFrame.from_dict(dct, orient='index', columns = columns)
    DF.set_index('Vertex', inplace=True)
    display(DF)
    print ("Średnia i maksymalna liczba kroków dla poszczególnych reguł:")
    DF2 = pd.DataFrame([srednia, maksymalna], columns = columns[1:6], index = ["średnia", "maksymalna"])
    display(HTML(DF2.to_html()))
        
########################################################################################################

def raport(P: InteractiveLPProblemStandardForm):
    set_random_seed(1)
    print("Problem jest dany w postaci standardowej:")
    pretty_print(P)
    is_set_of_feasible_solution_bounded(P)
    basic_sols = basic_solutions(P)
    print(f'Problem ma {len(basic_sols)} zbiorów bazowych dopuszczalnych')
    if len(basic_sols)==0:
        return None
    G, name = labelled_solution_graph(P)
    is_cycle_possible = True if len(G.all_simple_cycles())>0 else False
    show(G.plot(figsize=(8,8)))
    if is_cycle_possible:
        print('Wejście w cykl jest możliwe')
        print(f'Lista możliwych cykli: {G.all_simple_cycles()}')
    else:
        print("Wejście w cykl jest niemożliwe")
    r_name = {b: tuple((x+1 for x in n)) for n, b in name.items()}
    bland_edges, l_coeff_edges, l_increase_edges, steepest_edges, own_rule_edges = generate_edges(P, G, r_name)
    rule_edges = [bland_edges, l_coeff_edges, l_increase_edges, steepest_edges, own_rule_edges]
    rules = ['Blanda',  'largest coefficient', 'largest increase', 'steepest edge', 'lowest coefficient']
    print("\n Grafy dla różnych reguł przejścia z zaznaczonymi pivotami na niebiesko: \n")
    for i in range(5):
        print(f'Reguła {rules[i]}:')
        show(G.plot(edge_colors = {'blue': rule_edges[i]}, figsize=(8,8)))
        H = G.subgraph(G.vertices(), rule_edges[i])
        show(H.plot(figsize=(8,8), layout='tree'))
    print("\n Tabela przedstawiająca ile dana reguła wykona kroków dla różnych wierzchołków startowych: \n")
    print_table(P, G, r_name)