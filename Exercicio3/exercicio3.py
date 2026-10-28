import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")


@app.cell
def _():
    import z3

    # ==========================================================
    # EXERCICIO 3 - LOGICA COMPUTACIONAL
    # ==========================================================

    n = 8
    TIMEOUT = 15000

    # ==========================================================
    # ALINEA A - SFOTS
    # ==========================================================

    print("\n========== ALINEA A ==========")

    a = z3.BitVec("a", n)
    b = z3.BitVec("b", n)

    x = z3.BitVec("x", n)
    y = z3.BitVec("y", n)
    z = z3.BitVec("z", n)
    pc = z3.Int("pc")

    x1 = z3.BitVec("x1", n)
    y1 = z3.BitVec("y1", n)
    z1 = z3.BitVec("z1", n)
    pc1 = z3.Int("pc1")

    INIT = 0
    SKIP = 1
    LEFT = 2
    RIGHT = 3
    STOP = 4
    ERROR = 5

    # Estado inicial
    inicial = pc == INIT

    # Overflow sem sinal
    overflow_left = z3.Not(
        z3.BVMulNoOverflow(
            x, z3.BitVecVal(2, n), False
        )
    )

    overflow_right = z3.Not(
        z3.BVAddNoOverflow(z, x, False)
    )

    # INIT -> SKIP
    t_init = z3.And(
        pc == INIT,
        pc1 == SKIP,
        x1 == a,
        y1 == b,
        z1 == 0
    )

    # SKIP -> STOP
    t_stop = z3.And(
        pc == SKIP,
        y == 0,
        pc1 == STOP,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # SKIP -> LEFT
    t_left = z3.And(
        pc == SKIP,
        y != 0,
        (y & 1) == 0,
        pc1 == LEFT,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # SKIP -> RIGHT
    t_right = z3.And(
        pc == SKIP,
        y != 0,
        (y & 1) == 1,
        pc1 == RIGHT,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # LEFT -> SKIP
    t_left_ok = z3.And(
        pc == LEFT,
        z3.Not(overflow_left),
        pc1 == SKIP,
        x1 == x << 1,
        y1 == z3.LShR(y, 1),
        z1 == z
    )

    # RIGHT -> SKIP
    t_right_ok = z3.And(
        pc == RIGHT,
        z3.Not(overflow_right),
        pc1 == SKIP,
        x1 == x,
        y1 == y - 1,
        z1 == z + x
    )

    # LEFT -> ERROR
    t_left_error = z3.And(
        pc == LEFT,
        overflow_left,
        pc1 == ERROR,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # RIGHT -> ERROR
    t_right_error = z3.And(
        pc == RIGHT,
        overflow_right,
        pc1 == ERROR,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # Relacao de transicao
    transicao = z3.Or(
        t_init,
        t_stop,
        t_left,
        t_right,
        t_left_ok,
        t_right_ok,
        t_left_error,
        t_right_error
    )

    erro = pc == ERROR


    # ==========================================================
    # FUNCOES AUXILIARES
    # ==========================================================

    def resolver(*condicoes):
        s = z3.Solver()
        s.set(timeout=TIMEOUT)
        s.add(*condicoes)
        return s.check()


    def provar_inducao(prop, prop1, inicio):
        # Caso base
        base = resolver(inicio, z3.Not(prop))

        # Passo indutivo (k = 1)
        passo = resolver(
            prop,
            transicao,
            z3.Not(prop1)
        )

        return base, passo


    def fases_validas(p, v):
        return z3.And(
            z3.Implies(
                p == LEFT,
                z3.And(v != 0, (v & 1) == 0)
            ),
            z3.Implies(
                p == RIGHT,
                z3.And(v != 0, (v & 1) == 1)
            )
        )


    def estado_valido(p):
        return z3.Or(
            p == INIT,
            p == SKIP,
            p == LEFT,
            p == RIGHT,
            p == STOP,
            p == ERROR
        )


    # Verificacoes da alinea A
    resultado_a1 = resolver(inicial)
    resultado_a2 = resolver(transicao)

    print("Estado inicial:", resultado_a1)
    print("Relacao de transicao:", resultado_a2)


    # ==========================================================
    # ALINEA B - INVARIANTE POR K-INDUCAO
    # ==========================================================

    print("\n========== ALINEA B ==========")

    # Propriedade: x*y+z = a*b
    # Em INIT, as variaveis ainda nao foram inicializadas.

    def invariante_b(p, xx, yy, zz):

        igualdade = (
            xx * yy + zz == a * b
        )

        return z3.And(
            estado_valido(p),
            fases_validas(p, yy),
            z3.Or(
                p == INIT,
                igualdade
            )
        )


    prop_b = invariante_b(pc, x, y, z)
    prop_b1 = invariante_b(pc1, x1, y1, z1)

    base_b, passo_b = provar_inducao(
        prop_b,
        prop_b1,
        inicial
    )

    print("Caso base:", base_b)
    print("Passo indutivo:", passo_b)

    prova_b = (
        base_b == z3.unsat
        and passo_b == z3.unsat
    )

    if prova_b:
        print("Invariante provado por 1-inducao.")
    else:
        print("Invariante nao provado.")


    # ==========================================================
    # ALINEA C - SEGURANCA POR K-INDUCAO
    # ==========================================================

    print("\n========== ALINEA C ==========")

    limite = 2 ** (n // 2)

    entradas_pequenas = z3.And(
        z3.ULT(a, z3.BitVecVal(limite, n)),
        z3.ULT(b, z3.BitVecVal(limite, n))
    )

    # Alargamos os vetores para 16 bits.
    # Assim a igualdade nao perde os bits do produto.

    def ext(v):
        return z3.ZeroExt(n, v)


    def invariante_c(p, xx, yy, zz):

        igualdade = (
            ext(xx) * ext(yy) + ext(zz)
            ==
            ext(a) * ext(b)
        )

        return z3.And(
            entradas_pequenas,

            # O estado ERROR fica excluido
            z3.Or(
                p == INIT,
                p == SKIP,
                p == LEFT,
                p == RIGHT,
                p == STOP
            ),

            fases_validas(p, yy),

            z3.Or(
                p == INIT,
                igualdade
            )
        )


    prop_c = invariante_c(pc, x, y, z)
    prop_c1 = invariante_c(pc1, x1, y1, z1)

    base_c, passo_c = provar_inducao(
        prop_c,
        prop_c1,
        z3.And(inicial, entradas_pequenas)
    )

    print("Limite:", limite)
    print("Caso base:", base_c)
    print("Passo indutivo:", passo_c)

    prova_c = (
        base_c == z3.unsat
        and passo_c == z3.unsat
    )

    if prova_c:
        print("Seguranca provada por 1-inducao.")
        print("O estado ERROR e inacessivel.")
    else:
        print("Seguranca nao provada.")


    # ==========================================================
    # ALINEA D - TERMINACAO
    # ==========================================================

    print("\n========== ALINEA D ==========")

    # Funcao de ranking.
    # Diminui em cada transicao do automato.

    def ranking(p, v):

        numero = z3.BV2Int(
            v,
            is_signed=False
        )

        return z3.If(
            p == INIT,
            3 * (2 ** n) + 3,

            z3.If(
                p == SKIP,
                3 * numero + 2,

                z3.If(
                    z3.Or(
                        p == LEFT,
                        p == RIGHT
                    ),
                    3 * numero + 1,
                    0
                )
            )
        )


    r = ranking(pc, y)
    r1 = ranking(pc1, y1)

    # Verificar que o ranking e nao negativo
    resultado_d1 = resolver(
        estado_valido(pc),
        r < 0
    )

    # Verificar que diminui nas transicoes
    resultado_d2 = resolver(
        transicao,
        fases_validas(pc, y),
        r1 >= r
    )

    print("Ranking negativo:", resultado_d1)
    print("Ranking nao decrescente:", resultado_d2)

    prova_d = (
        resultado_d1 == z3.unsat
        and resultado_d2 == z3.unsat
    )

    if prova_d:
        print("Terminacao provada.")
    else:
        print("Terminacao nao provada.")


    # ==========================================================
    # RESULTADO FINAL
    # ==========================================================

    print("\n========== RESULTADO FINAL ==========")

    prova_a = (
        resultado_a1 == z3.sat
        and resultado_a2 == z3.sat
    )

    print(
        "Alinea A:",
        "SATISFAZIVEL" if prova_a else "VERIFICAR"
    )

    print(
        "Alinea B:",
        "PROVADA" if prova_b else "NAO PROVADA"
    )

    print(
        "Alinea C:",
        "PROVADA" if prova_c else "NAO PROVADA"
    )

    print(
        "Alinea D:",
        "PROVADA" if prova_d else "NAO PROVADA"
    )

    if prova_a and prova_b and prova_c and prova_d:
        print("\nTodas as verificacoes passaram.")
    else:
        print("\nExistem verificacoes por concluir.")
    return


if __name__ == "__main__":
    app.run()
