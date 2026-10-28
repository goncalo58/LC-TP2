import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")


@app.cell
def _():
    import z3

    # ==================================================
    # EXERCICIO 3 - LOGICA COMPUTACIONAL
    # Multiplicacao de inteiros com Z3
    # ==================================================

    # ==================================================
    # ALINEA A - CONSTRUCAO DO SFOTS
    # ==================================================

    n = 8

    # Variaveis de entrada
    a = z3.BitVec("a", n)
    b = z3.BitVec("b", n)

    # Variaveis do estado atual
    x = z3.BitVec("x", n)
    y = z3.BitVec("y", n)
    z = z3.BitVec("z", n)
    pc = z3.Int("pc")

    # Variaveis do estado seguinte
    x1 = z3.BitVec("x1", n)
    y1 = z3.BitVec("y1", n)
    z1 = z3.BitVec("z1", n)
    pc1 = z3.Int("pc1")

    # Estados do automato
    INIT = 0
    SKIP = 1
    LEFT = 2
    RIGHT = 3
    STOP = 4
    ERROR = 5

    # Estado inicial
    inicial = pc == INIT

    # Detecao de overflow sem sinal
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

    # Estado de erro
    erro = pc == ERROR

    print("ALINEA A")

    s = z3.Solver()
    s.add(inicial)
    print("Estado inicial:", s.check())

    s = z3.Solver()
    s.add(transicao)
    print("Relacao de transicao:", s.check())


    # ==================================================
    # FUNCOES AUXILIARES PARA AS PROVAS
    # ==================================================

    def verificar_base(propriedade, condicao=inicial):
        s = z3.Solver()
        s.add(condicao)
        s.add(z3.Not(propriedade))
        return s.check()


    def verificar_passo(propriedade, seguinte):
        s = z3.Solver()
        s.add(propriedade)
        s.add(transicao)
        s.add(z3.Not(seguinte))
        return s.check()


    # ==================================================
    # ALINEA B - INVARIANTE POR K-INDUCAO
    # ==================================================

    print("\nALINEA B")

    # A igualdade so e exigida depois da inicializacao
    propriedade_b = z3.Or(
        pc == INIT,
        x * y + z == a * b
    )

    propriedade_b1 = z3.Or(
        pc1 == INIT,
        x1 * y1 + z1 == a * b
    )

    base_b = verificar_base(propriedade_b)

    passo_b = verificar_passo(
        propriedade_b,
        propriedade_b1
    )

    print("Caso base:", base_b)
    print("Passo indutivo:", passo_b)

    if base_b == z3.unsat and passo_b == z3.unsat:
        print("Invariante demonstrado por 1-inducao.")
    else:
        print("A prova do invariante nao foi concluida.")


    # ==================================================
    # ALINEA C - SEGURANCA POR K-INDUCAO
    # ==================================================

    print("\nALINEA C")

    limite = 2 ** (n // 2)

    # Restricoes sobre as entradas
    entradas_pequenas = z3.And(
        z3.ULT(a, z3.BitVecVal(limite, n)),
        z3.ULT(b, z3.BitVecVal(limite, n))
    )

    # Conversao dos BitVecs para inteiros nao negativos
    def valor(v):
        return z3.BV2Int(v, is_signed=False)


    # Invariante reforcado
    def invariante_seguro(px, xx, yy, zz):

        estados_validos = z3.Or(
            px == INIT,
            px == SKIP,
            px == LEFT,
            px == RIGHT,
            px == STOP
        )

        igualdade = z3.Or(
            px == INIT,
            valor(xx) * valor(yy) + valor(zz)
            == valor(a) * valor(b)
        )

        # Condicoes associadas aos estados LEFT e RIGHT
        condicao_left = z3.Implies(
            px == LEFT,
            z3.And(
                yy != 0,
                (yy & 1) == 0
            )
        )

        condicao_right = z3.Implies(
            px == RIGHT,
            z3.And(
                yy != 0,
                (yy & 1) == 1
            )
        )

        return z3.And(
            entradas_pequenas,
            estados_validos,
            igualdade,
            condicao_left,
            condicao_right
        )


    seguro = invariante_seguro(pc, x, y, z)

    seguro1 = invariante_seguro(pc1, x1, y1, z1)

    # Caso base
    base_c = verificar_base(
        seguro,
        z3.And(inicial, entradas_pequenas)
    )

    # Passo indutivo
    passo_c = verificar_passo(seguro, seguro1)

    print("Limite:", limite)
    print("Caso base:", base_c)
    print("Passo indutivo:", passo_c)

    if base_c == z3.unsat and passo_c == z3.unsat:
        print("Seguranca demonstrada por 1-inducao.")
        print("O estado ERROR e inacessivel.")
    else:
        print("A prova de seguranca nao foi concluida.")


    # ==================================================
    # ALINEA D - TERMINACAO
    # ==================================================

    print("\nALINEA D")

    # Funcao de ranking
    def ranking(px, yy):

        valor_y = valor(yy)

        return z3.If(
            px == INIT,
            3 * (2 ** n) + 3,

            z3.If(
                px == SKIP,
                3 * valor_y + 2,

                z3.If(
                    z3.Or(px == LEFT, px == RIGHT),
                    3 * valor_y + 1,
                    0
                )
            )
        )


    r = ranking(pc, y)
    r1 = ranking(pc1, y1)

    # Verificar que o ranking nunca e negativo
    s = z3.Solver()
    s.add(r < 0)
    resultado_nao_negativo = s.check()

    # Verificar que diminui em cada transicao
    s = z3.Solver()
    condicoes_fases = z3.And(
        z3.Implies(
            pc == LEFT,
            z3.And(y != 0, (y & 1) == 0)
        ),
        z3.Implies(
            pc == RIGHT,
            z3.And(y != 0, (y & 1) == 1)
        )
    )

    s.add(transicao)
    s.add(condicoes_fases)
    s.add(r1 >= r)
    resultado_decrescente = s.check()

    print("Ranking negativo:", resultado_nao_negativo)
    print("Ranking nao decrescente:", resultado_decrescente)

    if (
        resultado_nao_negativo == z3.unsat
        and resultado_decrescente == z3.unsat
    ):
        print("Terminacao demonstrada.")
    else:
        print("A prova de terminacao nao foi concluida.")




    print("\n========== RESULTADO FINAL ==========")

    prova_b = (
        base_b == z3.unsat
        and passo_b == z3.unsat
    )

    prova_c = (
        base_c == z3.unsat
        and passo_c == z3.unsat
    )

    prova_d = (
        resultado_nao_negativo == z3.unsat
        and resultado_decrescente == z3.unsat
    )

    print("Alinea A: SFOTS construido")
    print("Alinea B:", "PROVADA" if prova_b else "NAO PROVADA")
    print("Alinea C:", "PROVADA" if prova_c else "NAO PROVADA")
    print("Alinea D:", "PROVADA" if prova_d else "NAO PROVADA")

    return


if __name__ == "__main__":
    app.run()
