import marimo

__generated_with = "0.24.2"
app = marimo.App(width="medium")


@app.cell
def _():
    import random
    import marimo as mo
    import numpy as np
    import matplotlib.pyplot as plt
    from matplotlib.colors import ListedColormap
    from matplotlib.patches import Patch
    from z3 import (
        And,
        Bool,
        BoolVal,
        Implies,
        Not,
        Or,
        PbEq,
        Solver,
        Xor,
        is_true,
        sat,
        unsat,
    )

    return (
        And,
        Bool,
        BoolVal,
        Implies,
        ListedColormap,
        Not,
        Or,
        Patch,
        PbEq,
        Solver,
        Xor,
        is_true,
        mo,
        np,
        plt,
        random,
        sat,
        unsat,
    )


@app.cell
def _(mo):
    mo.md(r"""
    # Exercício 1 — Game of Life Finitizado como FOTS / FSM Simbólica (Z3)

    Modelamos o autómato celular como um **sistema de transição proposicional (FSM simbólica)** com o solver SMT **Z3**.
    As propriedades são verificadas por **Bounded Model Checking (BMC)**, **K-Indução** e, no modo síncrono
    (determinista), também por **análise completa da órbita** (certificada em Z3).

    **Grelha** $(N+2)\times(N+2)$, índices $(i,j)\in\{0..N+1\}^2$:

    * **Normais** ($N^2$): $i,j\in\{1..N\}$, regra **B3/S23**; inicialmente vivas sse $i,j\le 3$.
    * **Iniciais** ($2N+1$): $i=0$ (com $j\le N$) ou $j=0$ (com $i\le N$); constantes aleatórias (prob. $1/2$).
    * **Finais** ($2N+3$): as restantes da moldura; constantes $0$.
    * **Estado de erro**: todas as células normais mortas.
    """)
    return


@app.cell
def _(mo):
    N_ui = mo.ui.slider(17, 30, value=17, step=1, label="Dimensão N (N > 16)")
    modo_ui = mo.ui.dropdown(
        options={
            "Síncrono (todas as células normais transitam)": "sync",
            "Assíncrono (uma e só uma célula normal transita)": "async",
        },
        value="Síncrono (todas as células normais transitam)",
        label="Relação de transição",
    )
    seed_ui = mo.ui.number(0, 10000, value=42, step=1, label="Seed (células iniciais)")
    mo.hstack([N_ui, modo_ui, seed_ui], justify="start", wrap=True)
    return N_ui, modo_ui, seed_ui


@app.cell
def _(
    And,
    Bool,
    BoolVal,
    Implies,
    N_ui,
    Not,
    Or,
    PbEq,
    Xor,
    is_true,
    modo_ui,
    np,
    random,
    seed_ui,
):
    # ------------------------------------------------------------------
    # Parâmetros
    # ------------------------------------------------------------------
    N = N_ui.value
    MODO = modo_ui.value
    SEED = int(seed_ui.value)

    def gerar_celulas_iniciais(n, seed):
        """Valores constantes (prob. 1/2) das 2N+1 células iniciais."""
        rng = random.Random(seed)
        ini = {}
        for j in range(n + 1):  # (0,0..N)  -> N+1 células
            ini[(0, j)] = rng.choice([True, False])
        for i in range(1, n + 1):  # (1..N,0) -> N células
            ini[(i, 0)] = rng.choice([True, False])
        return ini

    CELULAS_INICIAIS = gerar_celulas_iniciais(N, SEED)

    # ------------------------------------------------------------------
    # FOTS: declare / init / trans / error
    # ------------------------------------------------------------------
    def declare(t, n=N, iniciais=CELULAS_INICIAIS):
        """Estado no instante t: variáveis Z3 para as normais, constantes para a moldura."""
        state = {}
        for i in range(n + 2):
            for j in range(n + 2):
                if 1 <= i <= n and 1 <= j <= n:
                    state[(i, j)] = Bool(f"c_{t}_{i}_{j}")
                elif (i == 0 and j <= n) or (j == 0 and i <= n):
                    state[(i, j)] = BoolVal(iniciais[(i, j)])
                else:
                    state[(i, j)] = BoolVal(False)
        return state

    def init(state, n=N):
        """Vivas sse i,j <= 3; todas as outras normais mortas."""
        return And(
            [
                state[(i, j)] if (i <= 3 and j <= 3) else Not(state[(i, j)])
                for i in range(1, n + 1)
                for j in range(1, n + 1)
            ]
        )

    def regra_celula(state, i, j):
        """B3/S23 (vizinhança de Chebyshev, distância 1)."""
        viz = [
            state[(i + di, j + dj)]
            for di in (-1, 0, 1)
            for dj in (-1, 0, 1)
            if not (di == 0 and dj == 0)
        ]
        e3 = PbEq([(v, 1) for v in viz], 3)
        e2 = PbEq([(v, 1) for v in viz], 2)
        return Or(e3, And(state[(i, j)], e2))

    def trans_sync(s_curr, s_next, n):
        return And(
            [
                s_next[(i, j)] == regra_celula(s_curr, i, j)
                for i in range(1, n + 1)
                for j in range(1, n + 1)
            ]
        )

    def trans_async(s_curr, s_next, n):
        """
        Exatamente UMA célula normal muda de estado (para o valor dado pela regra B3/S23).
        Codificação compacta O(N^2) com variáveis de seleção sel_c.
        Se nenhuma célula pode mudar (estado estável) a relação faz 'stutter'
        (s_next = s_curr) para a relação ser total.
        """
        tag = str(s_curr[(1, 1)])
        cel = [(i, j) for i in range(1, n + 1) for j in range(1, n + 1)]
        sel = {c: Bool(f"sel_{tag}_{c[0]}_{c[1]}") for c in cel}
        regra = {c: regra_celula(s_curr, *c) for c in cel}
        restr = []
        for c in cel:
            restr.append(
                Implies(sel[c], And(Xor(s_curr[c], regra[c]), s_next[c] == regra[c]))
            )
            restr.append(Implies(Not(sel[c]), s_next[c] == s_curr[c]))
        ha_movel = Or([Xor(s_curr[c], regra[c]) for c in cel])
        restr.append(Implies(ha_movel, PbEq([(sel[c], 1) for c in cel], 1)))
        restr.append(Implies(Not(ha_movel), And([Not(sel[c]) for c in cel])))
        return And(restr)

    def trans(s_curr, s_next, modo=MODO, n=N):
        return trans_sync(s_curr, s_next, n) if modo == "sync" else trans_async(s_curr, s_next, n)

    def error_state(state, n=N):
        """Todas as células normais mortas."""
        return And([Not(state[(i, j)]) for i in range(1, n + 1) for j in range(1, n + 1)])

    def estavel(state, n=N):
        """Ponto fixo: nenhuma célula normal consegue mudar."""
        return And(
            [
                state[(i, j)] == regra_celula(state, i, j)
                for i in range(1, n + 1)
                for j in range(1, n + 1)
            ]
        )

    def extrair_G(model, state, n=N):
        """Modelo Z3 -> matriz (N+2)x(N+2) de 0/1."""
        G = np.zeros((n + 2, n + 2), dtype=np.int8)
        for i in range(n + 2):
            for j in range(n + 2):
                G[i, j] = 1 if is_true(model.eval(state[(i, j)], model_completion=True)) else 0
        return G

    return (
        CELULAS_INICIAIS,
        MODO,
        N,
        SEED,
        declare,
        error_state,
        estavel,
        extrair_G,
        init,
        trans,
    )


@app.cell
def _(ListedColormap, Patch, np, plt):
    # ------------------------------------------------------------------
    # Simulador rápido (numpy) + desenho da grelha
    # ------------------------------------------------------------------
    def grelha_inicial(n, iniciais):
        G = np.zeros((n + 2, n + 2), dtype=np.int8)
        for (i, j), v in iniciais.items():
            G[i, j] = int(v)
        G[1:4, 1:4] = 1
        return G

    def vizinhos_vivos(G):
        n = G.shape[0] - 2
        return sum(
            G[1 + di : n + 1 + di, 1 + dj : n + 1 + dj]
            for di in (-1, 0, 1)
            for dj in (-1, 0, 1)
            if (di, dj) != (0, 0)
        )

    def valor_regra(G):
        viz = vizinhos_vivos(G)
        c = G[1:-1, 1:-1]
        return ((viz == 3) | ((c == 1) & (viz == 2))).astype(np.int8)

    def passo_sync(G):
        H = G.copy()
        H[1:-1, 1:-1] = valor_regra(G)
        return H

    def passo_async(G, rng):
        """Escolhe (uniformemente) uma célula que possa mudar e aplica-lhe a regra."""
        novo = valor_regra(G)
        mudam = np.argwhere(novo != G[1:-1, 1:-1])
        H = G.copy()
        if len(mudam) == 0:
            return H, None  # estado estável (stutter)
        i, j = mudam[rng.randrange(len(mudam))]
        H[i + 1, j + 1] = novo[i, j]
        return H, (int(i) + 1, int(j) + 1)

    def orbita_sync(G0, max_passos=20000):
        """Sistema síncrono é determinista e finito: segue a trajetória até repetir."""
        vistos = {G0[1:-1, 1:-1].tobytes(): 0}
        hist, G = [G0], G0
        for t in range(1, max_passos + 1):
            G = passo_sync(G)
            chave = G[1:-1, 1:-1].tobytes()
            if chave in vistos:
                ini = vistos[chave]
                return {"hist": hist, "transiente": ini, "periodo": t - ini}
            vistos[chave] = t
            hist.append(G)
        return None

    def codigos(G):
        n = G.shape[0] - 2
        C = G.astype(int)
        for i in range(n + 2):
            for j in range(n + 2):
                if 1 <= i <= n and 1 <= j <= n:
                    continue
                if (i == 0 and j <= n) or (j == 0 and i <= n):
                    C[i, j] = 2 + int(G[i, j])  # inicial
                else:
                    C[i, j] = 4  # final
        return C

    def desenhar_grelha(G, titulo="Estado da grelha"):
        cmap = ListedColormap(["#f7f7f7", "#1b1b1b", "#c4dcf5", "#2563c9", "#e9c8c8"])
        legenda = [
            ("Normal morta", "#f7f7f7"),
            ("Normal viva", "#1b1b1b"),
            ("Inicial morta", "#c4dcf5"),
            ("Inicial viva", "#2563c9"),
            ("Final (0)", "#e9c8c8"),
        ]
        fig, ax = plt.subplots(figsize=(5.2, 5.2))
        ax.imshow(codigos(G), cmap=cmap, vmin=0, vmax=4, interpolation="nearest")
        ax.set_title(titulo, fontsize=10)
        ax.set_xlabel("j")
        ax.set_ylabel("i")
        ax.legend(
            handles=[Patch(fc=c, ec="#666", label=l) for l, c in legenda],
            loc="upper center",
            bbox_to_anchor=(0.5, -0.12),
            ncol=3,
            fontsize=8,
            frameon=False,
        )
        fig.tight_layout()
        plt.close(fig)
        return fig

    return (
        desenhar_grelha,
        grelha_inicial,
        orbita_sync,
        passo_async,
        passo_sync,
    )


@app.cell
def _(mo):
    mo.md(r"""
    ---
    ## Simulador interativo
    Usa os botões para avançar o autómato (no modo assíncrono é escolhida aleatoriamente
    uma célula que possa mudar). Mudar $N$, o modo ou a seed reinicia a simulação.
    """)
    return


@app.cell
def _(CELULAS_INICIAIS, N, SEED, grelha_inicial, mo, random):
    get_sim, set_sim = mo.state(
        {
            "G": grelha_inicial(N, CELULAS_INICIAIS),
            "t": 0,
            "ultimo": None,
            "rng": random.Random(SEED),
        }
    )
    return get_sim, set_sim


@app.cell
def _(
    CELULAS_INICIAIS,
    MODO,
    N,
    SEED,
    grelha_inicial,
    mo,
    passo_async,
    passo_sync,
    random,
    set_sim,
):
    def _avancar(s, k):
        G, ult = s["G"], None
        for _ in range(k):
            if MODO == "sync":
                G = passo_sync(G)
            else:
                G, ult = passo_async(G, s["rng"])
        return {"G": G, "t": s["t"] + k, "ultimo": ult, "rng": s["rng"]}

    def _reset(_):
        set_sim(
            {
                "G": grelha_inicial(N, CELULAS_INICIAIS),
                "t": 0,
                "ultimo": None,
                "rng": random.Random(SEED),
            }
        )

    btn_1 = mo.ui.button(label="▶ +1 passo", on_click=lambda _: set_sim(lambda s: _avancar(s, 1)))
    btn_10 = mo.ui.button(label="⏩ +10", on_click=lambda _: set_sim(lambda s: _avancar(s, 10)))
    btn_100 = mo.ui.button(label="⏭ +100", on_click=lambda _: set_sim(lambda s: _avancar(s, 100)))
    btn_reset = mo.ui.button(label="↺ Reiniciar", on_click=_reset)
    mo.hstack([btn_1, btn_10, btn_100, btn_reset], justify="start")
    return


@app.cell
def _(MODO, desenhar_grelha, get_sim, mo):
    _s = get_sim()
    _vivas = int(_s["G"][1:-1, 1:-1].sum())
    _extra = ""
    if MODO == "async":
        _extra = (
            f" | última célula alterada: `{_s['ultimo']}`"
            if _s["ultimo"]
            else " | (nenhuma célula alterada: estado estável ou início)"
        )
    _aviso = "  \n🚨 **ESTADO DE ERRO** (todas as normais mortas)" if _vivas == 0 else ""
    mo.vstack(
        [
            mo.md(f"**t = {_s['t']}** | células normais vivas: **{_vivas}**{_extra}{_aviso}"),
            desenhar_grelha(_s["G"], f"t = {_s['t']} (modo {MODO})"),
        ]
    )
    return


@app.cell
def _(mo):
    mo.md(r"""
    ---
    ## Verificação formal: BMC, K-indução, órbita completa
    """)
    return


@app.cell
def _(
    MODO,
    N,
    Not,
    Or,
    Solver,
    Xor,
    declare,
    error_state,
    extrair_G,
    init,
    np,
    sat,
    trans,
    unsat,
):
    def bmc(predicado, k_max, modo=MODO, n=N):
        """Existe execução de comprimento <= k_max que atinge `predicado`? (SAT = sim)."""
        solver = Solver()
        estados = [declare(0, n)]
        solver.add(init(estados[0], n))
        for k in range(k_max + 1):
            if k > 0:
                estados.append(declare(k, n))
                solver.add(trans(estados[k - 1], estados[k], modo, n))
            solver.push()
            solver.add(predicado(estados[k], n))
            if solver.check() == sat:
                m = solver.model()
                traj = [extrair_G(m, estados[t], n) for t in range(k + 1)]
                solver.pop()
                return {"sat": True, "k": k, "traj": traj}
            solver.pop()
        return {"sat": False, "k": k_max, "traj": None}

    def k_inducao_nunca_erro(k_max, modo=MODO, n=N):
        """K-indução para P = G(not erro)."""
        for k in range(1, k_max + 1):
            base = Solver()
            b = [declare(t, n) for t in range(k)]
            base.add(init(b[0], n))
            for t in range(k - 1):
                base.add(trans(b[t], b[t + 1], modo, n))
            base.add(Or([error_state(x, n) for x in b]))
            if base.check() == sat:
                return {"resultado": "FALSA (caso base falha)", "k": k}

            ind = Solver()
            s = [declare(f"ind_{t}", n) for t in range(k + 1)]
            for t in range(k):
                ind.add(Not(error_state(s[t], n)))
                ind.add(trans(s[t], s[t + 1], modo, n))
            ind.add(error_state(s[k], n))
            if ind.check() == unsat:
                return {"resultado": "PROVADA por k-indução", "k": k}
        return {"resultado": f"INCONCLUSIVA (k <= {k_max})", "k": k_max}

    def prova_1_orbita_z3(transiente, periodo, n=N):
        """Prova em Z3 que o erro nunca é alcançado (síncrono)."""
        L = transiente + periodo
        s = Solver()
        est = [declare(f"p1_{t}", n) for t in range(L + 1)]
        s.add(init(est[0], n))
        for t in range(L):
            s.add(trans(est[t], est[t + 1], "sync", n))

        # (a) nenhum s_0..s_{L-1} é erro
        s.push()
        s.add(Or([error_state(est[t], n) for t in range(L)]))
        sem_erro = s.check() == unsat
        s.pop()

        # (b) o ciclo fecha: s_L == s_T
        s.push()
        s.add(Or([Xor(est[L][(i, j)], est[transiente][(i, j)])
                  for i in range(1, n + 1) for j in range(1, n + 1)]))
        fecha = s.check() == unsat
        s.pop()

        return sem_erro and fecha

    def certificar_lasso_z3(transiente, periodo, n=N):
        """
        Certifica em Z3 a trajetória encontrada por simulação (modo síncrono):
        a partir de init, s_{T+P} = s_T (UNSAT da negação). Como a relação é determinista,
        isto prova que o ciclo de período P é alcançado após T passos.
        """
        L = transiente + periodo
        s = Solver()
        est = [declare(f"lasso_{t}", n) for t in range(L + 1)]
        s.add(init(est[0], n))
        for t in range(L):
            s.add(trans(est[t], est[t + 1], "sync", n))
        s.add(
            Or(
                [
                    Xor(est[L][(i, j)], est[transiente][(i, j)])
                    for i in range(1, n + 1)
                    for j in range(1, n + 1)
                ]
            )
        )
        return s.check() == unsat


    def analisar_orbita(orbita, n=N):
        """Células normais constantes ao longo do ciclo atrator."""
        ini, per = orbita["transiente"], orbita["periodo"]
        ciclo = np.stack([g[1:-1, 1:-1] for g in orbita["hist"][ini : ini + per]])
        vivas = [(int(i) + 1, int(j) + 1) for i, j in zip(*np.where(ciclo.all(axis=0)))]
        mortas = [(int(i) + 1, int(j) + 1) for i, j in zip(*np.where((ciclo == 0).all(axis=0)))]
        return vivas, mortas

    return (
        analisar_orbita,
        bmc,
        certificar_lasso_z3,
        k_inducao_nunca_erro,
        prova_1_orbita_z3,
    )


@app.cell
def _(mo):
    mo.md(r"""
    ---
    ### Propriedade 1 — *"Nunca se alcança o estado de erro"*
    """)
    return


@app.cell
def _(mo):
    k_slider = mo.ui.slider(1, 30, value=10, step=1, label="Profundidade K (BMC)")
    btn_prop1 = mo.ui.run_button(label="🚀 Verificar Propriedade 1")
    mo.hstack([k_slider, btn_prop1], justify="start")
    return btn_prop1, k_slider


@app.cell
def _(
    CELULAS_INICIAIS,
    MODO,
    N,
    SEED,
    bmc,
    btn_prop1,
    desenhar_grelha,
    error_state,
    grelha_inicial,
    k_inducao_nunca_erro,
    k_slider,
    mo,
    orbita_sync,
    prova_1_orbita_z3,
):
    mo.stop(not btn_prop1.value, mo.md("_Clica no botão para correr o Z3._"))

    _k = k_slider.value
    _bmc = bmc(error_state, _k, MODO, N)
    _kind = k_inducao_nunca_erro(min(_k, 2), MODO, N)  # k>=3 é impraticável (explosão do Z3)

    _out = [
        mo.md(
            f"#### Propriedade 1 (`modo={MODO}`, `N={N}`, `seed={SEED}`)\n"
            f"* **BMC (K={_k})**: "
            + (f"❌ erro alcançável em **{_bmc['k']}** passos" if _bmc["sat"] else f"sem erro até K={_k}")
            + f"\n* **K-indução (k≤{min(_k, 2)})**: {_kind['resultado']}"
        )
    ]

    if MODO == "sync":
        _orb = orbita_sync(grelha_inicial(N, CELULAS_INICIAIS))
        _linhas = []
        if _orb is None:
            _linhas.append("* **Órbita**: não convergiu em 20000 passos.")
        else:
            _T, _P = _orb["transiente"], _orb["periodo"]
            _t_erro = next(
                (t for t, g in enumerate(_orb["hist"]) if not g[1:-1, 1:-1].any()), None
            )

            # prova em Z3 (só se a órbita não for demasiado longa)
            _p1 = prova_1_orbita_z3(_T, _P, N) if _T + _P <= 800 else None

            if _p1 is True:
                _txt_z3 = "✅ provado em Z3: o erro não é alcançável e o ciclo fecha ⇒ **Propriedade 1 VERDADEIRA**"
            elif _p1 is False and _t_erro is not None:
                _txt_z3 = "❌ Z3 encontrou o erro na órbita ⇒ **Propriedade 1 FALSA**"
            elif _p1 is False:
                _txt_z3 = "⚠️ Z3 não confirmou (ver órbita abaixo)"
            else:
                _txt_z3 = "não certificado (órbita > 800 passos); resultado baseado na simulação"

            _linhas.append(f"* **Prova em Z3 (órbita)**: {_txt_z3}")
            _linhas.append(
                f"* **Órbita completa** (transiente={_T}, período={_P}): "
                + (
                    f"❌ erro no passo {_t_erro} ⇒ **Propriedade 1 FALSA**"
                    if _t_erro is not None
                    else "✅ o erro nunca ocorre ⇒ **Propriedade 1 VERDADEIRA** (sistema determinista e finito)"
                )
            )
        _out.append(mo.md("\n".join(_linhas)))

    if _bmc["sat"]:
        _kh = _bmc["k"]
        _out.append(
            mo.hstack(
                [
                    desenhar_grelha(_bmc["traj"][0], "s_0"),
                    desenhar_grelha(_bmc["traj"][_kh // 2], f"s_{_kh // 2}"),
                    desenhar_grelha(_bmc["traj"][_kh], f"s_{_kh} (ERRO)"),
                ],
                wrap=True,
            )
        )
    mo.vstack(_out)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ---
    ### Propriedade 2 — *"Nenhuma célula normal está permanentemente morta ou permanentemente viva"*

    * **Síncrono**: sistema determinista ⇒ a propriedade falha sse alguma célula é constante no **ciclo atrator**.
      A trajetória é certificada em Z3.
    * **Assíncrono**: sem hipótese de justiça, basta alcançar um **estado estável** (nenhuma célula pode mudar;
      relação faz *stutter*) para todas as células ficarem constantes para sempre. Procura-se por BMC.
    """)
    return


@app.cell
def _(mo):
    k2_slider = mo.ui.slider(1, 30, value=12, step=1, label="Profundidade K (modo assíncrono)")
    btn_prop2 = mo.ui.run_button(label="🔍 Verificar Propriedade 2")
    mo.hstack([k2_slider, btn_prop2], justify="start")
    return btn_prop2, k2_slider


@app.cell
def _(
    CELULAS_INICIAIS,
    MODO,
    N,
    SEED,
    analisar_orbita,
    bmc,
    btn_prop2,
    certificar_lasso_z3,
    desenhar_grelha,
    estavel,
    grelha_inicial,
    k2_slider,
    mo,
    orbita_sync,
):
    mo.stop(not btn_prop2.value, mo.md("_Clica no botão para correr a verificação._"))

    _out = [mo.md(f"#### Propriedade 2 (`modo={MODO}`, `N={N}`, `seed={SEED}`)")]



    if MODO == "sync":
        _orb = orbita_sync(grelha_inicial(N, CELULAS_INICIAIS))
        if _orb is None:
            _out.append(mo.md("* **Órbita**: não convergiu em 20000 passos."))
        else:
            _vivas, _mortas = analisar_orbita(_orb, N)
            _T, _P = _orb["transiente"], _orb["periodo"]
            _cert = (
                certificar_lasso_z3(_T, _P, N)
                if _T + _P <= 800
                else None
            )
            _cert_txt = {True: "✅ certificada em Z3", False: "⚠️ Z3 NÃO confirmou", None: "não certificada (trajetória > 800 passos)"}[_cert]
            _viola = bool(_vivas or _mortas)
            _out.append(
                mo.md(
                    f"* **Atrator** (transiente={_T}, período={_P}; {_cert_txt})\n"
                    f"* Permanentemente **vivas** ({len(_vivas)}): `{_vivas[:10]}`\n"
                    f"* Permanentemente **mortas** ({len(_mortas)}): `{_mortas[:10]}`\n\n"
                    + (
                        "❌ **Propriedade 2 FALSA** (há células constantes no atrator)."
                        if _viola
                        else "✅ **Propriedade 2 VERDADEIRA** (todas as células mudam no ciclo)."
                    )
                )
            )
            _out.append(desenhar_grelha(_orb["hist"][_T], f"Início do ciclo (t = {_T})"))
    else:
        _r = bmc(estavel, k2_slider.value, MODO, N)
        if _r["sat"]:
            _out.append(
                mo.md(
                    f"* **BMC**: estado estável alcançável em **{_r['k']}** passos ⇒ "
                    "❌ **Propriedade 2 FALSA** (todas as células ficam constantes)."
                )
            )
            _out.append(desenhar_grelha(_r["traj"][-1], f"Estado estável (t = {_r['k']})"))
        else:
            _out.append(
                mo.md(
                    f"* **BMC**: nenhum estado estável até K={k2_slider.value} (inconclusivo; "
                    "aumentar K). Nota: sem justiça, o escalonador pode ignorar células "
                    "indefinidamente, pelo que a propriedade só faz sentido sob hipótese de justiça."
                )
            )
    mo.vstack(_out)
    return


if __name__ == "__main__":
    app.run()
