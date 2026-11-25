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


@app.cell
def _():
    class Anel(Ts):
        def __init__(self, N, regenera=False):
            super().__init__(f'Anel{N}')
            assert N >= 2
            self.N, self.regenera = N, regenera
            self.w, self.c, self.t = {}, {}, {}   # i -> (pre, post)
            self.casos = []                       # (regra, i, formula)


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

        # 3) TODO: S.casos e S.Tr = z3.Or(*[f for _, _, f in S.casos])
        # 4) TODO: S.Bad

        return S

    return (anel,)


@app.cell
def _(anel):
    S = anel(2)
    s = z3.Solver()
    s.add(S.Init)
    print(s.check())   # sat
    print(s.model())   # w, c, t falsos, exceto t0


if __name__ == "__main__":
    app.run()
