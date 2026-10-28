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
    return


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
    return


if __name__ == "__main__":
    app.run()
