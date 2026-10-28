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


if __name__ == "__main__":
    app.run()
