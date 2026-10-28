import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")


@app.cell
def _():
    import z3

    # ============================================================
    # EXERCICIO 3 - LOGICA COMPUTACIONAL
    # Multiplicacao de inteiros usando Z3
    # ============================================================

    n = 8

    # ============================================================
    # ALINEA A - CONSTRUCAO DO SFOTS
    # ============================================================

    print("\n========== ALINEA A ==========")

    # Variaveis de entrada
    a = z3.BitVec("a", n)
    b = z3.BitVec("b", n)

    # Estado atual
    x = z3.BitVec("x", n)
    y = z3.BitVec("y", n)
    z = z3.BitVec("z", n)
    pc = z3.Int("pc")

    # Estado seguinte
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

    # Overflow sem sinal
    overflow_left = z3.Not(
        z3.BVMulNoOverflow(
            x,
            z3.BitVecVal(2, n),
            False
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

    # Relacao de transicao completa
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

    # Verificar estado inicial
    s = z3.Solver()
    s.set(timeout=5000)
    s.add(inicial)
    resultado_a1 = s.check()

    # Verificar transicoes
    s = z3.Solver()
    s.set(timeout=5000)
    s.add(transicao)
    resultado_a2 = s.check()

    print("Estado inicial:", resultado_a1)
    print("Relacao de transicao:", resultado_a2)


    # ============================================================
    # FUNCOES AUXILIARES
    # ============================================================

    # Condicoes que caracterizam os estados LEFT e RIGHT
    def fases_validas(p, v):
        return z3.And(
            z3.Implies(
                p == LEFT,
                z3.And(
                    v != 0,
                    (v & 1) == 0
                )
            ),
            z3.Implies(
                p == RIGHT,
                z3.And(
                    v != 0,
                    (v & 1) == 1
                )
            )
        )


    # Caso base da inducao
    def verificar_base(propriedade, condicao):
        s = z3.Solver()
        s.set(timeout=5000)

        s.add(condicao)
        s.add(z3.Not(propriedade))

        return s.check()


    # Passo indutivo
    def verificar_inducao(propriedade, seguinte):
        s = z3.Solver()
        s.set(timeout=5000)

        s.add(propriedade)
        s.add(transicao)
        s.add(z3.Not(seguinte))

        return s.check()


    # ============================================================
    # ALINEA B - INVARIANTE POR K-INDUCAO
    # ============================================================

    print("\n========== ALINEA B ==========")

    # Propriedade:
    # x * y + z = a * b

    # A igualdade so e exigida depois da inicializacao.
    # Acrescentamos as condicoes das fases LEFT e RIGHT.

    propriedade_b = z3.And(
        z3.Or(
            pc == INIT,
            x * y + z == a * b
        ),
        fases_validas(pc, y)
    )

    propriedade_b1 = z3.And(
        z3.Or(
            pc1 == INIT,
            x1 * y1 + z1 == a * b
        ),
        fases_validas(pc1, y1)
    )

    # Caso base
    base_b = verificar_base(
        propriedade_b,
        inicial
    )

    # Passo indutivo: k = 1
    inducao_b = verificar_inducao(
        propriedade_b,
        propriedade_b1
    )

    print("Caso base:", base_b)
    print("Passo indutivo:", inducao_b)

    prova_b = (
        base_b == z3.unsat
        and inducao_b == z3.unsat
    )

    if prova_b:
        print("Invariante demonstrado por 1-inducao.")
    else:
        print("Invariante nao demonstrado.")


    # ============================================================
    # ALINEA C - SEGURANCA POR K-INDUCAO
    # ============================================================

    print("\n========== ALINEA C ==========")

    # Condicoes iniciais:
    # a < 2^(n/2)
    # b < 2^(n/2)

    limite = 2 ** (n // 2)

    entradas_pequenas = z3.And(
        z3.ULT(
            a,
            z3.BitVecVal(limite, n)
        ),
        z3.ULT(
            b,
            z3.BitVecVal(limite, n)
        )
    )

    # Usamos vetores de 16 bits para evitar perda de bits
    # na igualdade utilizada para provar a seguranca.

    def alargar(v):
        return z3.ZeroExt(n, v)


    # Invariante reforcado da seguranca
    def invariante_seguro(p, xx, yy, zz):

        # Estados permitidos
        estados_validos = z3.Or(
            p == INIT,
            p == SKIP,
            p == LEFT,
            p == RIGHT,
            p == STOP
        )

        # Igualdade sem overflow de 8 bits
        igualdade = (
            alargar(xx) * alargar(yy) + alargar(zz)
            ==
            alargar(a) * alargar(b)
        )

        return z3.And(
            entradas_pequenas,
            estados_validos,
            z3.Or(
                p == INIT,
                igualdade
            ),
            fases_validas(p, yy)
        )


    # Propriedade no estado atual
    seguro = invariante_seguro(
        pc, x, y, z
    )

    # Propriedade no estado seguinte
    seguro1 = invariante_seguro(
        pc1, x1, y1, z1
    )

    # Caso base
    base_c = verificar_base(
        seguro,
        z3.And(
            inicial,
            entradas_pequenas
        )
    )

    # Passo indutivo: k = 1
    inducao_c = verificar_inducao(
        seguro,
        seguro1
    )

    print("Limite dos valores iniciais:", limite)
    print("Caso base:", base_c)
    print("Passo indutivo:", inducao_c)

    prova_c = (
        base_c == z3.unsat
        and inducao_c == z3.unsat
    )

    if prova_c:
        print("Seguranca demonstrada por 1-inducao.")
        print("O estado ERROR e inacessivel.")
    else:
        print("Seguranca nao demonstrada.")


    # ============================================================
    # ALINEA D - TERMINACAO DO PROGRAMA
    # ============================================================

    print("\n========== ALINEA D ==========")

    # Para provar a terminacao usamos uma funcao de ranking.
    # O ranking deve ser nao negativo e diminuir
    # em todas as transicoes possiveis.

    def ranking(p, v):

        # Converter y para inteiro nao negativo
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


    # Ranking atual e seguinte
    r = ranking(pc, y)
    r1 = ranking(pc1, y1)

    # Verificar se o ranking pode ser negativo
    s = z3.Solver()
    s.set(timeout=5000)

    s.add(r < 0)

    resultado_ranking = s.check()

    print("Ranking negativo:", resultado_ranking)

    # Verificar se o ranking diminui
    s = z3.Solver()
    s.set(timeout=5000)

    s.add(transicao)
    s.add(fases_validas(pc, y))
    s.add(r1 >= r)

    resultado_decrescente = s.check()

    print("Ranking nao decrescente:", resultado_decrescente)

    prova_d = (
        resultado_ranking == z3.unsat
        and resultado_decrescente == z3.unsat
    )

    if prova_d:
        print("Terminacao demonstrada.")
    else:
        print("Terminacao nao demonstrada.")


    # ============================================================
    # RESULTADO FINAL
    # ============================================================

    print("\n========== RESULTADO FINAL ==========")

    prova_a = (
        resultado_a1 == z3.sat
        and resultado_a2 == z3.sat
    )

    print(
        "Alinea A:",
        "MODELO SATISFAZIVEL" if prova_a
        else "VERIFICAR"
    )

    print(
        "Alinea B:",
        "PROVADA" if prova_b
        else "NAO PROVADA"
    )

    print(
        "Alinea C:",
        "PROVADA" if prova_c
        else "NAO PROVADA"
    )

    print(
        "Alinea D:",
        "PROVADA" if prova_d
        else "NAO PROVADA"
    )

    if prova_a and prova_b and prova_c and prova_d:
        print("\nTodas as verificacoes passaram!")
    else:
        print("\nExistem verificacoes por concluir.")
    return


if __name__ == "__main__":
    app.run()
