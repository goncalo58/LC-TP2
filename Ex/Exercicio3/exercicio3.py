import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")


@app.cell
def _():

    import z3

    # Tamanho dos vetores de bits
    n = 8

    # Variaveis iniciais
    a = z3.BitVec("a", n)
    b = z3.BitVec("b", n)

    # Variaveis do algoritmo
    x = z3.BitVec("x", n)
    y = z3.BitVec("y", n)
    z = z3.BitVec("z", n)

    print("Variaveis criadas com sucesso!")
    return a, b, n, x, y, z, z3


@app.cell
def _():
    import z3

    # Tamanho dos vetores de bits
    n = 8

    # Valores de entrada
    a = z3.BitVec("a", n)
    b = z3.BitVec("b", n)

    # Variáveis do algoritmo
    x = z3.BitVec("x", n)
    y = z3.BitVec("y", n)
    z = z3.BitVec("z", n)

    # Identificador do estado do autómato
    pc = z3.Int("pc")

    # Identificadores dos estados
    INIT = 0
    SKIP = 1
    LEFT = 2
    RIGHT = 3
    STOP = 4
    ERROR = 5

    # Estado inicial
    inicial = z3.And(
        pc == INIT,
        z3.UGE(a, 0),
        z3.UGE(b, 0)
    )

    print("Variáveis e estado inicial definidos com sucesso!")
    return ERROR, INIT, LEFT, RIGHT, SKIP, STOP, a, b, n, pc, x, y, z, z3


@app.cell
def _(INIT, LEFT, RIGHT, SKIP, STOP, a, b, n, pc, x, y, z, z3):
    # Variaveis do estado seguinte
    x1 = z3.BitVec("x1", n)
    y1 = z3.BitVec("y1", n)
    z1 = z3.BitVec("z1", n)
    pc1 = z3.Int("pc1")

    # Transicao INIT -> SKIP
    t_init = z3.And(
        pc == INIT,
        pc1 == SKIP,
        x1 == a,
        y1 == b,
        z1 == 0
    )

    # Transicao SKIP -> STOP
    t_stop = z3.And(
        pc == SKIP,
        y == 0,
        pc1 == STOP,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # Transicao SKIP -> LEFT
    t_left = z3.And(
        pc == SKIP,
        y != 0,
        y & 1 == 0,
        pc1 == LEFT,
        x1 == x,
        y1 == y,
        z1 == z
    )

    # Transicao SKIP -> RIGHT
    t_right = z3.And(
        pc == SKIP,
        y != 0,
        y & 1 == 1,
        pc1 == RIGHT,
        x1 == x,
        y1 == y,
        z1 == z
    )

    print("Primeiras transicoes definidas!")
    return pc1, t_init, t_left, t_right, t_stop, x1, y1, z1


@app.cell
def _(ERROR, LEFT, RIGHT, SKIP, n, pc, pc1, x, x1, y, y1, z, z1, z3):
    # Overflow na multiplicacao por 2
    overflow_left = z3.ULT(
        z3.BitVecVal(2**(n-1) - 1, n),
        x
    )

    # Overflow na soma z + x
    overflow_right = z3.Not(
        z3.BVAddNoOverflow(z, x, True)
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

    print("Operacoes e overflow definidos!")
    return t_left_error, t_left_ok, t_right_error, t_right_ok


@app.cell
def _(
    ERROR,
    pc,
    t_init,
    t_left,
    t_left_error,
    t_left_ok,
    t_right,
    t_right_error,
    t_right_ok,
    t_stop,
    z3,
):
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

    print("Relacao de transicao criada!")
    print("Estado de erro definido!")
    return


if __name__ == "__main__":
    app.run()
