import marimo

__generated_with = "0.26.0"
app = marimo.App()

with app.setup:
    import marimo as mo
    import sys
    import z3


@app.class_definition
class HtmlStr(object):
    def __init__(self, s):
        self._s = str(s)
        self._s = self._s.replace('\n', '<br/>')
 
    def _repr_html_(self):
        return self._s
 
    def __repr__(self):
        return repr(self._s)
    def __str__(self):
        return str(self._s)


@app.function
def chc_to_str(chc):
    if z3.in_html_mode():
        return chc_to_html(chc)
    else:
        return chc_to_txt(chc)


@app.function
def chc_to_html(chc):
    import io
    out = io.StringIO()
 
    for cls in chc:
        print(cls, '<br/>', file=out)
 
    return HtmlStr(out.getvalue())


@app.function
def chc_to_txt(chc):
    import io
    out = io.StringIO()
    for cls in chc:
        print(cls, file=out)
    return out.getvalue()


@app.class_definition
class SpacerProof(object):
    def __init__(self, pf_ast):
        # strip off last mp to false
        self._ast = pf_ast.children()[0]
 
    def _get_fact(self, ast):
        return ast.children()[-1]
 
    def _to_dot_rec(self, ast, graph, visited):
        if ast.get_id() in visited:
            return
 
        visited.add(ast.get_id())
 
        dst = str(self._get_fact(ast).get_id())
        kids = ast.children()
        for k in kids[1:-1]:
            k_fact = self._get_fact(k)
            if k_fact.get_id() not in visited:
                graph.node(str(k_fact.get_id()), str(k_fact))
                visited.add(k_fact.get_id())
                self._to_dot_rec(k, graph, visited)
            graph.edge(str(k_fact.get_id()), dst)
 
    def to_dot(self):
        import graphviz
        g = graphviz.Digraph()
 
        visited = set()
 
        fact = self._get_fact(self._ast)
        id = fact.get_id()
        g.node(str(id), str(fact))
        visited.add(id)
        self._to_dot_rec(self._ast, g, visited)
        return g
 
    def _repr_mimebundle_(self, include, exclude, **kwargs):
        return self.to_dot()._repr_mimebundle_(include, exclude, **kwargs)
 
    def __str__(self):
        return str(self.to_dot())
    def raw(self):
        return self._ast


@app.cell
def _():
    # proof mode must be enabled before any expressions are created
    z3.set_param(proof=True)
    z3.set_param(model=True)
    # print expressions with HTML
    z3.set_html_mode(True)
 
    # wrapper to solve CHC constraints and extract result
    def solve_horn(chc, pp=False, q3=False, max_unfold=10, verbosity=0):
        z3.set_param(verbose=verbosity)
 
        s = z3.SolverFor('HORN')
        s.set('engine', 'spacer')
        s.set('spacer.order_children', 2)
        if not pp:
            s.set('xform.inline_eager', False)
            s.set('xform.inline_linear', False)
            s.set('xform.slice', False)
 
        if max_unfold > 0:
            s.set('spacer.max_level', max_unfold)
 
        if q3:
            # allow quantified variables in pobs
            s.set('spacer.ground_pobs', False)
            # enable quantified generalization
            s.set('spacer.q3.use_qgen', True)
 
        # add constraints to solver
        s.add(chc)
        if verbosity > 0:
            print(s.sexpr())
        # run solver
        res = s.check()
        # extract model or proof
        answer = None
        if res == z3.sat:
            answer = s.model()
        elif res == z3.unsat:
            answer = s.proof()
        return res, answer

    return (solve_horn,)


@app.class_definition
class Ts(object):
    """A transition system

    Example usage
    >>> T = Ts('Ts0')
    >>> x, x_out = T.add_var(z3.IntSort(), name='x')
    >>> T.Init = x <= 0
    >>> T.Tr = z3.And(x < 5, x_out == x + 1)
    >>> T.Bad = x >= 10
    >>> T                                   #doctest: +NORMALIZE_WHITESPACE
    Transition System: Ts0
        Init: v_0 <= 0
        Bad: v_0 >= 10
        Tr: And(v_0 < 5, v_out_0 == v_0 + 1)
    """
    def __init__(self, name='Ts'):
        # string name
        self.name = name
        # state variables (pair of input and output)
        self._vars = []
        # inputs
        self._inputs = []
        # a map from optional names to state variables
        self._named_vars = dict()
 
        # maps state variable index to optional name
        self._var_names = list()
 
        # Transition relation
        self.Tr = z3.BoolVal(True)
        # Initial condition
        self.Init = z3.BoolVal(True)
        # Bad states
        self.Bad = z3.BoolVal(False)
 
 
    def add_var(self, sort, name=None):
        '''Add a state variable of a given sort. Returns a pair (pre, post)
           of a pre- and post- state versions of the variable
        '''
        pre, post = self._new_var_name(name=name)
        v_in = z3.Const(pre, sort)
        v_out = z3.Const(post, sort)
        self._vars.append((v_in, v_out))
        self._var_names.append(name)
        if name is not None:
            self._named_vars[name] = (v_in, v_out) 
 
        return (v_in, v_out)
 
    def get_var(self, idx):
        """Returns a pair of pre- and post-variables with a given index or name

        If idx is not an int it is interpreted as a name.
        Otherwise, it is interpreted as a variable index.

        >>> T = Ts('Ts0')
        >>> x, x_out = T.add_var(z3.IntSort(), name='x')
        >>> y, y_out = T.add_var(z3.IntSort(), name='y')
        >>> x
        v_0

        >>> T.get_var(1)
        (v_1, v_out_1)

        >>> T.get_var('x')
        (v_0, v_out_0)

        """
        if isinstance(idx, int):
            return self._vars[idx]
        elif idx in self._named_vars:
            return self._named_vars[idx]
        return None
 
    def get_var_name(self, idx):
        if idx < len(self._var_names):
            return self._var_names[idx]
        return None
 
    def get_pre_var(self, idx):
        """Returns a pre-state variable with a given name/index"""
        res = self.get_var(idx)
        if res is not None:
            return res[0]
        return None
 
    def get_pre_vars(self, vars):
        """Returns a tuple of pre-state variables with given names"""
        return (self.get_pre_var(v) for v in vars.split())
 
    def get_post_var(self, idx):
        """Returns a post-state variable with a given name"""
        res = self.get_var(idx)
        if res is not None:
            return res[1]
        return None
 
    def add_input(self, sort, name=None):
        '''Add an input of a given sort'''
        v = z3.Const(self._new_input_name(name=name), sort)
        self._inputs.append(v)
        return v
 
    def inputs(self):
        return self._inputs
    def pre_vars(self):
        return [u for (u, v) in self._vars]
    def post_vars(self):
        return [v for (u, v) in self._vars]
    def vars(self):
        return self.pre_vars() + self.post_vars()
    def pre_post_vars(self):
        return self._vars
    def all(self):
        return self.vars() + self.inputs()
    def sig(self):
        return [v.sort() for (u, v) in self._vars]
    def to_post(self, e):
        '''Rename expression over pre-state variables to post-state variables

        >>> T = Ts('Ts0')
        >>> x, x_out = T.add_var(z3.IntSort(), 'x')
        >>> y, y_out = T.add_var(z3.IntSort(), 'y')
        >>> e = x > y
        >>> T.to_post(x > y)
        v_out_0 > v_out_1
        '''
        return z3.substitute(e, *self._vars)
 
    def _new_input_name(self, name=None):
        if name is not None:
            return str(name)
        else:
            return self._mk_input_name(len(self._inputs))
 
    def _mk_input_name(self, idx):
        return 'i_' + str(idx)
 
    def _new_var_name(self, name=None):
        if name is not None:
            assert name not in self._named_vars
            assert str(name) not in self._named_vars
            return str(name), str(name) + "'" 
        else:
            idx = len(self._vars)
            return self._mk_var_name(idx), self._mk_post_var_name(idx)
 
    def _mk_var_name(self, idx):
        return 'v_' + str(idx)
    def _mk_post_var_name(self, idx):
        return 'v_out_' + str(idx)
 
    def __repr__(self):
        return 'Transition System: ' + self.name + '\n' + \
            '\tInit: ' + str(self.Init) + '\n' + \
            '\tBad: ' + str(self.Bad) + '\n' + \
            '\tTr: ' + str(self.Tr)
 
    def __str__(self):
        return repr(self)


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    ## Interpolante de Craig

    Existem duas fórmulas \(A\) e \(B\), tais que:

    $$
    A \land B \text{ é insatisfatível (UNSAT)}
    $$

    O **Interpolante de Craig** de \(A\) e \(B\) é uma fórmula \(Itp\) que satisfaz as seguintes condições:

    1. \(A \Rightarrow Itp\)
    2. \(Itp \land B \Rightarrow \bot\)
    3. \(Itp\) contém apenas os símbolos comuns a \(A\) e \(B\).

    ### Caracterização através de CHC

    \(Itp\) é um interpolante de \(A\) e \(B\) sse satisfaz as seguintes CHC (*Constrained Horn Clauses*):

    $$
    \forall a,c:\quad A(a,c) \Rightarrow Itp(c)
    $$

    $$
    \forall b,c:\quad Itp(c) \land B(b,c) \Rightarrow \bot
    $$

    Onde:

    - \(c\) representa os símbolos partilhados entre \(A\) e \(B\);
    - \(a\) representa os símbolos que pertencem apenas a \(A\);
    - \(b\) representa os símbolos que pertencem apenas a \(B\).
    """)


@app.function
def free_arith_vars(fml):
    seen = set([])
    vars = set([])
    int_sort = z3.IntSort()

    def fv(seen, vars, f):
        if f in seen:
            return
        seen = seen | {f}
        if f.sort().eq(int_sort) and f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            vars = vars | {f}
        for ch in f.children():
            fv(seen, vars, ch)
    fv(seen, vars, fml)
    return vars


@app.cell
def _(solve_horn):
    def interpolate(A,B):
        As = free_arith_vars(A)
        Bs = free_arith_vars(B)

        shared = [s for s in As & Bs]

        Itp = z3.Function('Itp', [s.sort() for s in shared] + [z3.BoolSort()])
        left = z3.ForAll([a for a in As], z3.Implies(A, Itp(shared)))
        right = z3.ForAll([b for b in Bs], z3.Implies(Itp(shared), z3.Not(B)))

        res, ans = solve_horn([left,right])

        if res == z3.sat:
            return ans.eval(Itp(shared))
        return None

    return (interpolate,)


@app.cell
def _(interpolate):
    a,b,x,y = z3.Ints('a b x y')
    itp = interpolate(z3.And(a < x, x < b), z3.And(b < a))

    if itp != None:
        print(itp)
    else:
        print("Good")


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    # Princípio de Indução
    O problema de reachability simbólico é um tuplo (v, Init, Tr, Bad) onde
    1. V é o conjunto de variáveis de estado
    2. Init é um predicado sobre v que descreve o conjunto de estados iniciais
    3. Tr é um predicado entre v e v' que descreve a relação de transição
    4. Bad é um predicado sobre v que descreve o conjunto de estados de erro

    **Princípio de Indução: P é seguro** sse existe uma fórmula Inv(v) tal que:
    1. (Initiation) Init => Inv
    2. (Induction) Inv ^ Tr => Inv'
    3. (Safety) Inv ^ Bad => False

    A esta fórmula chama-se uma hipótese indutiva. Encontrar a hipótese indutiva correta reduz-se a decidir a satisfazbilidade da CHC que segue da definição do princípio de indução.
    """)


@app.function
def mk_ts0(safe=True):
    T = Ts('Ts0')
    x, x_out = T.add_var(z3.IntSort(), name='x')
    T.Init = x <= 0
    T.Tr = z3.And(x < 5, x_out == x +1)
    if safe:
        T.Bad = x >= 10
    else:
        T.Bad = x >= 4
    return T


@app.cell
def _():
    ts0 = mk_ts0()
    HtmlStr(ts0)
    return (ts0,)


@app.function
def vc_gen(T:Ts):
    Inv = z3.Function('Inv', *(T.sig() + [z3.BoolSort()]))

    InvPre = Inv(*T.pre_vars())
    InvPost = Inv(*T.post_vars())

    all_vars = T.all()
    vc_init = z3.ForAll(all_vars, z3.Implies(T.Init, InvPre))
    vc_ind = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre, T.Tr), InvPost))
    vc_bad = z3.ForAll(all_vars, z3.Implies(z3.And(InvPre,T.Bad), z3.BoolVal(False)))

    return [vc_init, vc_ind, vc_bad], InvPre


@app.cell
def _(ts0):
    vc, inv = vc_gen(ts0)
    return inv, vc


@app.cell
def _(vc):
    chc_to_str(vc)


@app.cell
def _(solve_horn, vc):
    res, ans = solve_horn(vc)
    return ans, res


@app.cell
def _(res):
    res


@app.cell
def _(ans):
    ans


@app.cell
def _(ans, inv):
    ans.eval(inv)


@app.cell
def _():
    ts1 = mk_ts0(safe=False)
    vc1, inv1 = vc_gen(ts1)
    return (vc1,)


@app.cell
def _(vc1):
    chc_to_str(vc1)


@app.cell
def _(solve_horn, vc1):
    res_1, ans_1 = solve_horn(vc1)
    res_1
    return (ans_1,)


@app.cell
def _(ans_1):
    import os
    graphviz_bin = os.path.join(os.environ['CONDA_PREFIX'], 'Library', 'bin')
    os.environ['PATH'] = graphviz_bin + os.pathsep + os.environ['PATH']
    sp = SpacerProof(ans_1)
    sp


if __name__ == "__main__":
    app.run()
