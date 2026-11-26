# /// script
# dependencies = ["marimo", "z3-solver"]
# requires-python = ">=3.14"
# ///

import marimo

__generated_with = "0.26.0"
app = marimo.App(width="medium")

with app.setup:
    import marimo as mo
    import sys
    import z3
    from CHC import Ts, HtmlStr


@app.cell(hide_code=True)
def _():
    mo.md(r"""
    Vamos começar a construção do SFOTS proposicional com a classe definida para CHC definida na aula.
    """)


@app.class_definition
class Anel(Ts):
    def __init__(self, N, regenera=False):
        super().__init__(f'Anel{N}')
        assert N >= 2
        self.N, self.regenera = N, regenera
        self.w, self.c, self.t = {}, {}, {}   # i -> (pre, post)
        self.casos = []                       # (regra, i, formula)


@app.function
def anel(N, regenera=False):
    S = Anel(N, regenera)

    # 1) variáveis: por cada processo, w_i, c_i, t_i
    for i in range(N):
        S.w[i] = S.add_var(z3.BoolSort(), name=f'w{i}')
        S.c[i] = S.add_var(z3.BoolSort(), name=f'c{i}')
        S.t[i] = S.add_var(z3.BoolSort(), name=f't{i}')

    # 2) estado inicial (só variáveis pre-estado, ou seja, índice [0])
    cond = []
    for i in range(N):
        cond.append(z3.Not(S.w[i][0]))
        cond.append(z3.Not(S.c[i][0]))
        cond.append(S.t[i][0] if i == 0 else z3.Not(S.t[i][0]))
    S.Init = z3.And(*cond)

    # 3) transições
    constroi_tr(S)

    # 4) TODO: S.Bad

    return S


@app.function
def moldura(S, alteradas):
    """Tudo o que a regra não altera fica igual (v_out == v)."""
    ids = {v_out.get_id() for v_out in alteradas}
    return z3.And(*[v_out == v for v, v_out in S.pre_post_vars()
                    if v_out.get_id() not in ids])


@app.function
def regra_pedir(S, i):
    w, w_out = S.w[i]
    c, c_out = S.c[i]
    condicao = z3.And(z3.Not(w), z3.Not(c))
    efeito = w_out
    return z3.And(condicao, efeito, moldura(S, [w_out]))


@app.function
def regra_entrar(S, i):
    w, w_out = S.w[i]
    c, c_out = S.c[i]
    t, t_out = S.t[i]
    condicao = z3.And(w, t)
    efeito = z3.And(z3.Not(w_out), c_out)
    return z3.And(condicao, efeito, moldura(S, [w_out, c_out]))


@app.function
def regra_sair(S, i):
    w, w_out = S.w[i]
    c, c_out = S.c[i]
    t, t_out = S.t[i]
    tm, tm_out = S.t[(i + 1) % S.N]  # t_{i+1 mod N}
    condicao = c
    efeito = z3.And(z3.Not(c_out), z3.Not(t_out), tm_out)
    return z3.And(condicao, efeito, moldura(S, [c_out, t_out, tm_out]))


@app.function
def regra_passar(S, i):
    w, w_out = S.w[i]
    c, c_out = S.c[i]
    t, t_out = S.t[i]
    tm, tm_out = S.t[(i + 1) % S.N]  # t_{i+1 mod N}
    condicao = z3.And(z3.Not(w), z3.Not(c), t)
    efeito = z3.And(z3.Not(t_out), tm_out)
    return z3.And(condicao, efeito, moldura(S, [t_out, tm_out]))


@app.function
def regras_anel(regenera):
    """Dicionário nome -> função. Tem de ser criado dentro de uma função
    para ser visível a partir de outras @app.function."""
    regras = {
        'pedir': regra_pedir,
        'entrar': regra_entrar,
        'sair': regra_sair,
        'passar': regra_passar,
    }
    if regenera:
        pass  # TODO: regras['regenerar'] = regra_regenerar (quando existir)
    return regras


@app.function
def constroi_tr(S):
    """Preenche S.casos com (regra, i, formula) e define S.Tr como o Or deles."""
    for nome, f in regras_anel(S.regenera).items():
        for i in range(S.N):
            S.casos.append((nome, i, f(S, i)))
    S.Tr = z3.Or(*[f for _, _, f in S.casos])


@app.function
def caso(S, regra, i):
    """Fórmula do caso (regra, processo i); útil para testes e para o BMC."""
    return next(f for r, j, f in S.casos if r == regra and j == i)


@app.cell
def _():
    S = anel(2)
    print(len(S.casos))   # esperado: 8

    s = z3.Solver()
    s.add(S.Init, caso(S, 'passar', 0))
    print(s.check())      # esperado: sat
    print(s.model())      # só passa o testemunho: t0 False, t1 True (no estado seguinte)


if __name__ == "__main__":
    app.run()