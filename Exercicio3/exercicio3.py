import marimo

__generated_with = "0.24.2"
app = marimo.App(width="medium")


@app.cell
def _():
    import z3

    # ==========================================================
    # EXERCICIO 3 - LOGICA COMPUTACIONAL
    # ==========================================================

    n = 8
    TIMEOUT = 120000

    # ==========================================================
    # ALINEA A - SFOTS
    # ==========================================================

    print("\n========== ALINEA A ==========")

    a = z3.BitVec("a", n)
    b = z3.BitVec("b", n)
    a1 = z3.BitVec("a1", n)
    b1 = z3.BitVec("b1", n)


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
    inicial = z3.And(pc == INIT, a >= 0, b >= 0)

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
    mesmas_ab = z3.And(a1 == a, b1 == b)

    transicao = z3.And(
        mesmas_ab,
        z3.Or(
            t_init,
            t_stop,
            t_left,
            t_right,
            t_left_ok,
            t_right_ok,
            t_left_error,
            t_right_error
        )
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

    #esta alinea pode dar unknown em algum pc , vai depender do timeout

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

        # ----------------------------------------------------------
        # ALINEA D (cont.) - ANIMACAO: SEM DEADLOCK FORA DOS FINAIS
        # ----------------------------------------------------------

        print("\n========== ALINEA D (ANIMACAO) ==========")

        nao_final = z3.Or(pc == INIT, pc == SKIP, pc == LEFT, pc == RIGHT)

        tem_sucessor = z3.Exists([pc1, x1, y1, z1, a1, b1], transicao)

        # (i) nenhum estado nao final fica bloqueado
        resultado_d3 = resolver(nao_final, z3.Not(tem_sucessor))

        # (ii) STOP e ERROR sao realmente finais
        resultado_d4 = resolver(z3.Or(pc == STOP, pc == ERROR), transicao)

        print("Deadlock fora dos finais:", resultado_d3)
        print("Finais com sucessor:", resultado_d4)

        prova_animacao = (
            prova_d
            and resultado_d3 == z3.unsat
            and resultado_d4 == z3.unsat
        )

        if prova_animacao:
            print("Animacao provada: o programa termina para quaisquer a, b.")
        else:
            print("Animacao nao provada.")



    # ----------------------------------------------------------
    # ALINEA D (cont.) - ANIMACAO: SEM DEADLOCK FORA DOS FINAIS
    # ----------------------------------------------------------

    print("\n========== ALINEA D (ANIMACAO) ==========")

    nao_final = z3.Or(pc == INIT, pc == SKIP, pc == LEFT, pc == RIGHT)

    tem_sucessor = z3.Exists([pc1, x1, y1, z1, a1, b1], transicao)

    # (i) nenhum estado nao final fica bloqueado
    resultado_d3 = resolver(nao_final, z3.Not(tem_sucessor))

    # (ii) STOP e ERROR sao realmente finais
    resultado_d4 = resolver(z3.Or(pc == STOP, pc == ERROR), transicao)

    print("Deadlock fora dos finais:", resultado_d3)
    print("Finais com sucessor:", resultado_d4)

    prova_animacao = (
        prova_d
        and resultado_d3 == z3.unsat
        and resultado_d4 == z3.unsat
    )

    if prova_animacao:
        print("Animacao provada: o programa termina para quaisquer a, b.")
    else:
        print("Animacao nao provada.")





    # ==========================================================
    # ALINEA E - CORRECAO: EM STOP, z = a*b
    # ==========================================================

    print("\n========== ALINEA E (CORRECAO) ==========")

    # Invariante auxiliar J: STOP so e alcancado com y == 0
    def invariante_j(p, yy):
        return z3.Implies(p == STOP, yy == 0)

    j = invariante_j(pc, y)
    j1 = invariante_j(pc1, y1)

    base_e, passo_e = provar_inducao(j, j1, inicial)

    print("J - Caso base:", base_e)
    print("J - Passo indutivo:", passo_e)

    # (i) Modulo 2^n: usa o invariante B (provado na alinea B)
    resultado_e1 = resolver(prop_b, j, pc == STOP, z != a * b)

    # (ii) Entradas pequenas: usa o invariante C (16 bits, sem perder bits)
    resultado_e2 = resolver(
        prop_c, j, pc == STOP,
        ext(z) != ext(a) * ext(b)
    )

    print("STOP e z != a*b (mod 2^n):", resultado_e1)
    print("STOP e z != a*b (inteiros, a,b pequenos):", resultado_e2)

    prova_e = (
        prova_b and prova_c
        and base_e == z3.unsat and passo_e == z3.unsat
        and resultado_e1 == z3.unsat and resultado_e2 == z3.unsat
    )

    if prova_e:
        print("Correcao provada: ao chegar a STOP, z = a*b.")
    else:
        print("Correcao nao provada.")


    # ==========================================================
    # ALINEA F - K-INDUCAO COM k VARIAVEL
    # ==========================================================

    print("\n========== ALINEA F (K-INDUCAO) ==========")

    # Relacao com sumidouros em STOP e ERROR (so para a k-inducao).
    sumidouro = z3.And(
        z3.Or(pc == STOP, pc == ERROR),
        pc1 == pc, x1 == x, y1 == y, z1 == z, a1 == a, b1 == b
    )
    transicao_k = z3.Or(transicao, sumidouro)

    VARS_ATUAL = [pc, x, y, z, a, b]
    VARS_PROX = [pc1, x1, y1, z1, a1, b1]


    def estado(i):
        return [
            z3.Int(f"pc_{i}"),
            z3.BitVec(f"x_{i}", n),
            z3.BitVec(f"y_{i}", n),
            z3.BitVec(f"z_{i}", n),
            z3.BitVec(f"a_{i}", n),
            z3.BitVec(f"b_{i}", n),
        ]


    def em(expr, atual, prox=None):
        # instancia uma expressao nas variaveis do passo i (e i+1)
        pares = list(zip(VARS_ATUAL, atual))
        if prox is not None:
            pares += list(zip(VARS_PROX, prox))
        return z3.substitute(expr, *pares)


    def k_inducao(prop, k, inicio):
        # Caso base: os k primeiros estados do traco satisfazem prop
        S = [estado(i) for i in range(k)]
        s = z3.Solver()
        s.set(timeout=TIMEOUT)
        s.add(em(inicio, S[0]))
        for i in range(k - 1):
            s.add(em(transicao_k, S[i], S[i + 1]))
        s.add(z3.Or([z3.Not(em(prop, S[i])) for i in range(k)]))
        base = s.check()

        # Passo: prop em k estados consecutivos => prop no seguinte
        S = [estado(i) for i in range(k + 1)]
        s = z3.Solver()
        s.set(timeout=TIMEOUT)
        for i in range(k):
            s.add(em(prop, S[i]))
            s.add(em(transicao_k, S[i], S[i + 1]))
        s.add(z3.Not(em(prop, S[k])))
        passo = s.check()

        return base, passo


    inicio_c = z3.And(inicial, entradas_pequenas)

    # (i) Verificacao cruzada: o invariante reforcado da C, com k = 1
    base_f0, passo_f0 = k_inducao(prop_c, 1, inicio_c)
    print("Cruzada (invariante C, k=1):", base_f0, passo_f0)

    # (ii) Propriedade simples (pc != ERROR): procurar o menor k
    seguro = pc != ERROR
    k_min = None

    for k in range(1, 61):
        base_k, passo_k = k_inducao(seguro, k, inicio_c)
        print(f"k={k:2d}  base: {base_k}  passo: {passo_k}")
        if base_k != z3.unsat:
            break
        if passo_k == z3.unsat:
            k_min = k
            break

    prova_f = (
        base_f0 == z3.unsat and passo_f0 == z3.unsat
        and k_min is not None
    )

    if k_min is not None:
        print(f"pc != ERROR e {k_min}-indutivo (menor k testado).")
    else:
        print("pc != ERROR nao ficou provado ate k=60.")


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



    print("Animacao:", "PROVADA" if prova_animacao else "NAO PROVADA")

    print("Alinea E:", "PROVADA" if prova_e else "NAO PROVADA")

    print("Alinea F:", "PROVADA" if prova_f else "NAO PROVADA")

    if prova_a and prova_b and prova_c and prova_d and prova_animacao and prova_e and prova_f:
        print("\nTodas as verificacoes passaram.")
    else:
        print("\nExistem verificacoes por concluir.")
    return


if __name__ == "__main__":
    app.run()
