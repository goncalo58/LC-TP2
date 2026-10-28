import marimo

__generated_with = "0.25.1"
app = marimo.App(width="medium")


@app.cell
def _():
    return


@app.cell
def _():
    from typing import NamedTuple

    import marimo as mo
    import matplotlib.pyplot as plt
    import numpy as np
    from matplotlib.colors import ListedColormap
    from matplotlib.patches import Patch, Rectangle

    return ListedColormap, NamedTuple, Patch, Rectangle, mo, np, plt


@app.cell
def _(mo):
    mo.md(r"""
    # Exercício 1 — Game of Life finitizado como FSM

    **Modelo.** Consideramos a grelha *completa* de índices $(i,j)\in\{0,\dots,N+1\}^2$:

    | Tipo de célula | Índices | Nº | Valor |
    |---|---|---|---|
    | **normal** | $1\le i,j\le N$ | $N^2$ | evolui segundo B3/S23 |
    | **inicial** | $i=0$ ou $j=0$, com $i,j\le N$ | $2N+1$ | constante, sorteada com $P(\text{viva})=\tfrac12$ |
    | **final** | $i=N+1$ ou $j=N+1$ | $2N+3$ | constante $0$ |

    Como as células iniciais e finais são constantes, o **estado** da FSM é só a matriz
    das $N^2$ células normais: $S=\{0,1\}^{N\times N}$.

    * **Estado inicial** $s_0$: viva sse $i,j\le 3$.
    * **Estado de erro**: todas as células normais mortas.
    * **Regra**: $f(c,n)= (n=3)\ \lor\ (c\land n=2)$, vizinhança de Chebyshev ($\max(|\Delta i|,|\Delta j|)=1$,
      ou seja, 8 vizinhos, que podem ser células iniciais/finais).
    * **Transição síncrona**: $T(s)=\{\,s' : s'_{ij}=f(s_{ij},n_{ij}(s))\ \forall (i,j)\,\}$ (determinista).
    * **Transição assíncrona**: $T(s)=\{\,s[(i,j)\mapsto f(s_{ij},n_{ij}(s))] : (i,j)\in\{1..N\}^2\}$
      (não-determinista: o sistema escolhe *uma* célula a atualizar).

    O modo é escolhido pelo parâmetro **Modo de transição** abaixo.
    """)
    return


@app.cell
def _(ListedColormap, NamedTuple, Patch, Rectangle, np, plt):
    # --- Parâmetro "interpretação das transições" -------------------------
    MODO_SINCRONO = "síncrono (todas as células)"
    MODO_ASSINCRONO = "assíncrono (uma célula)"

    # --- Estado e fronteira -----------------------------------------------
    def make_border_values(N, seed):
        """Valores constantes das 2N+1 células iniciais.

        Ordem: (0,0),(0,1),...,(0,N) seguidas de (1,0),(2,0),...,(N,0).
        """
        rng = np.random.default_rng(seed)
        return rng.random(2 * N + 1) < 0.5

    def initial_normal(N):
        """Estado inicial s0: células normais com i,j <= 3 vivas."""
        g = np.zeros((N, N), dtype=bool)
        g[:3, :3] = True  # índices 1..3 (1-based) == 0..2 (0-based)
        return g

    def build_padded(normal, border):
        """Grelha completa (N+2)x(N+2): iniciais + normais + finais (a 0)."""
        N = normal.shape[0]
        P = np.zeros((N + 2, N + 2), dtype=bool)  # finais ficam a 0
        P[0, : N + 1] = border[: N + 1]
        P[1 : N + 1, 0] = border[N + 1 :]
        P[1 : N + 1, 1 : N + 1] = normal
        return P

    # --- Regra B3/S23 ------------------------------------------------------
    def neighbour_counts(P):
        """Nº de vizinhos vivos (Chebyshev = 1) das células normais."""
        N = P.shape[0] - 2
        Pi = P.astype(np.uint8)
        c = np.zeros((N, N), dtype=np.uint8)
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                if di or dj:
                    c += Pi[1 + di : N + 1 + di, 1 + dj : N + 1 + dj]
        return c

    def life_rule(alive, counts):
        """B3/S23: nasce com 3; sobrevive com 2 ou 3."""
        return (counts == 3) | (alive & (counts == 2))

    def next_values(normal, border):
        """Valor que cada célula normal tomaria se fosse atualizada agora."""
        return life_rule(normal, neighbour_counts(build_padded(normal, border)))

    # --- Transições da FSM ---------------------------------------------------
    def step_sync(normal, border):
        """Interpretação (ii): todas as células transitam em simultâneo."""
        return next_values(normal, border)

    def step_async(normal, border, rng, only_unstable=True):
        """Interpretação (i): uma e só uma célula normal transita.

        only_unstable=True  -> escolhe entre as células cuja regra muda o valor
        only_unstable=False -> escolhe qualquer célula (pode ser um no-op)
        Devolve (novo_estado, (i,j) 1-based da célula escolhida | None se ponto fixo).
        """
        N = normal.shape[0]
        nxt = next_values(normal, border)
        if only_unstable:
            cand = np.flatnonzero((nxt != normal).ravel())
            if cand.size == 0:
                return normal, None  # ponto fixo: nenhuma célula pode mudar
        else:
            cand = np.arange(normal.size)
        k = int(rng.choice(cand))
        new = normal.copy()
        new.flat[k] = nxt.flat[k]
        return new, (k // N + 1, k % N + 1)

    class Snapshot(NamedTuple):
        normal: np.ndarray
        t: int
        history: tuple  # nº de células vivas em cada instante
        last_cell: tuple | None

    def fresh_snapshot(N):
        s0 = initial_normal(N)
        return Snapshot(s0, 0, (int(s0.sum()),), None)

    def advance(snap, border, mode, only_unstable, seed, steps):
        """Avança `steps` transições (função pura: devolve novo Snapshot)."""
        normal, t, hist, last = snap
        hist = list(hist)
        for _ in range(steps):
            if mode == MODO_SINCRONO:
                normal, last = step_sync(normal, border), None
            else:
                rng = np.random.default_rng([seed, t])  # reprodutível
                normal, last = step_async(normal, border, rng, only_unstable)
                if last is None:
                    break
            t += 1
            hist.append(int(normal.sum()))
        return Snapshot(normal, t, tuple(hist), last)

    # --- Visualização -------------------------------------------------------
    CMAP = ListedColormap(
        ["#f7f7f7", "#1b1b1b", "#c4dcf5", "#2563c9", "#e9c8c8"]
    )
    LEGENDA = [
        ("normal morta", "#f7f7f7"),
        ("normal viva", "#1b1b1b"),
        ("inicial morta", "#c4dcf5"),
        ("inicial viva", "#2563c9"),
        ("final (sempre 0)", "#e9c8c8"),
    ]

    def plot_grid(snap, border):
        N = snap.normal.shape[0]
        codes = np.full((N + 2, N + 2), 4, dtype=int)  # 4 = final
        codes[0, : N + 1] = 2 + border[: N + 1]
        codes[1 : N + 1, 0] = 2 + border[N + 1 :]
        codes[1 : N + 1, 1 : N + 1] = snap.normal.astype(int)

        fig, (ax, ax2) = plt.subplots(
            1, 2, figsize=(12, 5.4), gridspec_kw={"width_ratios": [1.25, 1]}
        )
        ax.imshow(codes, cmap=CMAP, vmin=0, vmax=4, interpolation="nearest")
        ax.set_xticks(np.arange(-0.5, N + 2, 1), minor=True)
        ax.set_yticks(np.arange(-0.5, N + 2, 1), minor=True)
        ax.grid(which="minor", color="#9a9a9a", linewidth=0.3)
        ax.tick_params(which="minor", length=0)
        ticks = list(range(0, N + 2, 1 if N <= 20 else 5))
        ax.set_xticks(ticks)
        ax.set_yticks(ticks)
        ax.tick_params(labelsize=7)
        ax.set_xlabel("j")
        ax.set_ylabel("i")
        ax.set_title(f"Grelha (t = {snap.t})")
        if snap.last_cell is not None:  # destaca a última célula atualizada
            i, j = snap.last_cell
            ax.add_patch(
                Rectangle((j - 0.5, i - 0.5), 1, 1, fill=False, ec="red", lw=2)
            )
        ax.legend(
            handles=[Patch(fc=c, ec="#777", label=l) for l, c in LEGENDA],
            loc="upper center",
            bbox_to_anchor=(0.5, -0.09),
            ncol=3,
            fontsize=7,
            frameon=False,
        )

        ax2.plot(range(len(snap.history)), snap.history, color="#2563c9")
        ax2.set_title("Células normais vivas ao longo do tempo")
        ax2.set_xlabel("transição")
        ax2.set_ylabel("nº de células vivas")
        ax2.grid(alpha=0.3)
        fig.tight_layout()
        plt.close(fig)
        return fig

    # --- Análise de propriedades: modo SÍNCRONO (exata) ---------------------
    def analyse_sync(N, border, max_steps=20000):
        """No modo síncrono a FSM é determinista -> a execução é
        'transiente + ciclo'. Detetando o ciclo decidimos EXATAMENTE:
          (i)  se o estado de erro é alguma vez visitado;
          (ii) que células ficam permanentemente mortas/vivas (no ciclo).
        """
        s = initial_normal(N)
        seen = {s.tobytes(): 0}
        traj = [s]
        error_t = 0 if not s.any() else None
        for t in range(1, max_steps + 1):
            s = step_sync(s, border)
            if error_t is None and not s.any():
                error_t = t
            key = s.tobytes()
            if key in seen:
                mu = seen[key]
                cyc = np.stack(traj[mu:t])
                return dict(
                    cycle_found=True,
                    transient=mu,
                    period=t - mu,
                    error_t=error_t,
                    perm_alive=np.all(cyc, axis=0),
                    perm_dead=~np.any(cyc, axis=0),
                )
            seen[key] = t
            traj.append(s)
        return dict(cycle_found=False, steps=max_steps, error_t=error_t)

    # --- Análise: modo ASSÍNCRONO, N grande (simulação + pesquisa) ------------
    def async_random_runs(N, border, runs, max_steps, only_unstable, seed):
        """Execuções aleatórias. Só pode REFUTAR propriedades (não prova)."""
        n_error = n_fixed = n_open = 0
        fixed_example = None
        for r in range(runs):
            rng = np.random.default_rng([seed, 1000 + r])
            s = initial_normal(N)
            outcome = "open"
            for _ in range(max_steps):
                if not s.any():
                    outcome = "error"
                    break
                nxt = next_values(s, border)
                if not (nxt != s).any():
                    outcome = "fixed"
                    break
                s, _c = step_async(s, border, rng, only_unstable)
            if outcome == "error":
                n_error += 1
            elif outcome == "fixed":
                n_fixed += 1
                if fixed_example is None:
                    fixed_example = s
            else:
                n_open += 1
        return dict(n_error=n_error, n_fixed=n_fixed, n_open=n_open,
                    fixed_example=fixed_example)

    def beam_search_error(N, border, beam=32, max_depth=300, seed=0):
        """Pesquisa em feixe por um *escalonamento* assíncrono que atinja o
        estado de erro (heurística: minimizar nº de células vivas).
        Se encontra, o caminho é um contra-exemplo concreto de (i)."""
        rng = np.random.default_rng(seed)
        s0 = initial_normal(N)
        nodes = [(None, None)]  # id -> (pai, célula k)
        frontier = [(s0, 0)]
        visited = {hash(s0.tobytes())}
        explored = 1

        def path_to(nid, k_last):
            ks = [k_last]
            while nid != 0:
                nid, k = nodes[nid]
                ks.append(k)
            return [(k // N + 1, k % N + 1) for k in reversed(ks)]

        for depth in range(1, max_depth + 1):
            cand = []
            for state, nid in frontier:
                nxt = next_values(state, border)
                for k in np.flatnonzero((nxt != state).ravel()):
                    child = state.copy()
                    child.flat[k] = nxt.flat[k]
                    h = hash(child.tobytes())
                    if h in visited:
                        continue
                    visited.add(h)
                    explored += 1
                    cnt = int(child.sum())
                    if cnt == 0:
                        return dict(found=True, path=path_to(nid, int(k)),
                                    explored=explored)
                    cand.append((cnt + rng.random(), child, nid, int(k)))
            if not cand:
                return dict(found=False, explored=explored, depth=depth,
                            reason="espaço alcançável esgotado")
            cand.sort(key=lambda x: x[0])
            frontier = []
            for _score, child, nid, k in cand[:beam]:
                nodes.append((nid, k))
                frontier.append((child, len(nodes) - 1))
        return dict(found=False, explored=explored, depth=max_depth,
                    reason="profundidade máxima atingida")

    # --- Verificação EXAUSTIVA (só N pequeno) --------------------------------
    def explore_fsm(N, border, mode, max_states=400_000):
        """Explora todo o grafo alcançável a partir de s0 e verifica:

        (i)  o estado de erro (tudo morto) é alcançável?
        (ii) para cada célula c e valor v: existe uma execução infinita em que
             c fica para sempre = v a partir de algum instante? (CTL: EF EG c=v)
             Só se consideram transições *efetivas* (que mudam o estado);
             um estado sem transições efetivas é um ponto fixo (laço implícito).
        Exato para o grafo explorado; inconclusivo se `truncated`.
        """
        n = N * N
        ar = np.arange(n, dtype=np.int64)

        def encode(vec):
            return int(vec.astype(np.int64) @ (np.int64(1) << ar))

        def decode(s):
            return ((np.int64(s) >> ar) & 1).astype(bool)

        s0 = encode(initial_normal(N).ravel())
        index, states, succ = {s0: 0}, [s0], []
        truncated = False
        i = 0
        while i < len(states):
            s = states[i]
            cur = decode(s)
            nxt = next_values(cur.reshape(N, N), border).ravel()
            if mode == MODO_SINCRONO:
                ns = [x for x in [encode(nxt)] if x != s]
            else:
                ns = [s ^ (1 << int(k)) for k in np.flatnonzero(nxt != cur)]
            row = []
            for x in ns:
                j = index.get(x)
                if j is None:
                    if len(states) >= max_states:
                        truncated = True
                        continue
                    j = len(states)
                    index[x] = j
                    states.append(x)
                row.append(j)
            succ.append(row)
            i += 1

        M = len(states)
        if truncated:
            return dict(truncated=True, n_states=M)

        K = max(1, max(len(r) for r in succ))
        S = np.full((M, K), -1, dtype=np.int64)
        for a, r in enumerate(succ):
            S[a, : len(r)] = r
        valid = S >= 0
        terminal = ~valid.any(axis=1)
        safeS = np.where(valid, S, 0)

        def EG(inset):
            cur = inset.copy()
            while True:
                has = (valid & cur[safeS]).any(axis=1)
                new = cur & (has | terminal)
                if np.array_equal(new, cur):
                    return cur
                cur = new

        arr = np.array(states, dtype=np.int64)
        bits = ((arr[:, None] >> ar[None, :]) & 1).astype(bool)
        perm_dead, perm_alive = [], []
        for k in range(n):
            cell = (k // N + 1, k % N + 1)
            if EG(~bits[:, k]).any():
                perm_dead.append(cell)
            if EG(bits[:, k]).any():
                perm_alive.append(cell)
        return dict(
            truncated=False,
            n_states=M,
            n_transitions=int(valid.sum()),
            n_fixed_points=int(terminal.sum()),
            error_reachable=(0 in index),
            perm_dead=perm_dead,
            perm_alive=perm_alive,
        )

    def fmt_cells(cells, limit=12):
        cells = list(cells)
        txt = ", ".join(f"({i},{j})" for i, j in cells[:limit])
        return txt + (f", … (+{len(cells) - limit})" if len(cells) > limit else "")

    def mask_to_cells(mask):
        return [(int(i) + 1, int(j) + 1) for i, j in zip(*np.nonzero(mask))]

    return (
        MODO_ASSINCRONO,
        MODO_SINCRONO,
        advance,
        analyse_sync,
        async_random_runs,
        beam_search_error,
        explore_fsm,
        fmt_cells,
        fresh_snapshot,
        make_border_values,
        mask_to_cells,
        next_values,
        plot_grid,
    )


@app.cell
def _(MODO_ASSINCRONO, MODO_SINCRONO, mo):
    N_slider = mo.ui.slider(17, 40, value=20, label="N (tamanho da grelha, N > 16)")
    mode_dropdown = mo.ui.dropdown(
        [MODO_SINCRONO, MODO_ASSINCRONO],
        value=MODO_SINCRONO,
        label="Modo de transição",
    )
    seed_input = mo.ui.number(0, 10**6, value=42, step=1, label="Semente (células iniciais)")
    only_unstable = mo.ui.checkbox(
        value=True, label="Assíncrono: escolher só células cuja regra altera o estado"
    )
    steps_slider = mo.ui.slider(1, 200, value=10, label="Passos por clique em «Executar»")
    return N_slider, mode_dropdown, only_unstable, seed_input, steps_slider


@app.cell
def _(
    N_slider,
    fresh_snapshot,
    make_border_values,
    mo,
    mode_dropdown,
    seed_input,
):
    N = N_slider.value
    mode = mode_dropdown.value
    seed = int(seed_input.value)
    border = make_border_values(N, seed)
    get_state, set_state = mo.state(fresh_snapshot(N))
    return N, border, get_state, mode, seed, set_state


@app.cell
def _(
    N,
    advance,
    border,
    fresh_snapshot,
    mo,
    mode,
    only_unstable,
    seed,
    set_state,
    steps_slider,
):
    step_btn = mo.ui.button(
        label="▶ Avançar 1 passo",
        on_click=lambda _v: set_state(
            lambda s: advance(s, border, mode, only_unstable.value, seed, 1)
        ),
    )
    run_btn = mo.ui.button(
        label="⏩ Executar k passos",
        on_click=lambda _v: set_state(
            lambda s: advance(s, border, mode, only_unstable.value, seed, steps_slider.value)
        ),
    )
    reset_btn = mo.ui.button(
        label="↺ Reiniciar",
        on_click=lambda _v: set_state(lambda s: fresh_snapshot(N)),
    )
    return reset_btn, run_btn, step_btn


@app.cell
def _(
    MODO_SINCRONO,
    N,
    N_slider,
    border,
    get_state,
    mo,
    mode,
    mode_dropdown,
    next_values,
    only_unstable,
    plot_grid,
    reset_btn,
    run_btn,
    seed_input,
    step_btn,
    steps_slider,
):
    snap = get_state()
    _nxt = next_values(snap.normal, border)
    _unstable = int((_nxt != snap.normal).sum())
    _alive = int(snap.normal.sum())

    _flags = []
    if _alive == 0:
        _flags.append("🔴 **ESTADO DE ERRO** (todas as células normais mortas)")
    if _unstable == 0:
        _flags.append("🟡 **ponto fixo** (nenhuma célula pode mudar)")
    _last = (
        f"última célula atualizada: `{snap.last_cell}`"
        if snap.last_cell
        else ("todas atualizadas em simultâneo" if mode == MODO_SINCRONO and snap.t else "—")
    )

    mo.vstack(
        [
            mo.md("## Simulador"),
            mo.hstack([N_slider, mode_dropdown, seed_input], justify="start", wrap=True),
            mo.hstack([only_unstable, steps_slider], justify="start", wrap=True),
            mo.hstack([step_btn, run_btn, reset_btn], justify="start"),
            mo.md(
                f"**t = {snap.t}** · vivas: **{_alive}**/{N * N} · "
                f"células instáveis: {_unstable} · {_last}  \n" + "  \n".join(_flags)
            ),
            plot_grid(snap, border),
        ]
    )
    return


@app.cell
def _(mo):
    mo.md(r"""
    ---
    ## Propriedades (alínea b)

    1. **(i)** Nunca se alcança o estado de erro: $\mathbf{AG}\ \neg\text{erro}$
    2. **(ii)** Nenhuma célula normal fica permanentemente morta ou viva:
       $\forall c.\ \neg\mathbf{FG}(c=0)\ \land\ \neg\mathbf{FG}(c=1)$

    Com $N>16$ há $2^{N^2}$ estados (>$10^{86}$), pelo que **não é possível verificação exaustiva**.
    Usa-se por isso:

    * **modo síncrono** → a FSM é determinista, logo a execução é *transiente + ciclo*; detetar o ciclo
      decide **exatamente** (i) e (ii) para essa semente;
    * **modo assíncrono** → simulação aleatória + pesquisa em feixe: **só conseguem refutar** (contra-exemplos), não provar;
    * **N pequeno (3–4)** → verificação exaustiva do grafo de estados (secção seguinte), útil para validar a lógica.
    """)
    return


@app.cell
def _(mo):
    analysis_btn = mo.ui.run_button(label="🔍 Analisar propriedades (N e modo atuais)")
    n_runs = mo.ui.slider(5, 60, value=20, label="Simulações aleatórias (assíncrono)")
    sim_steps = mo.ui.slider(500, 10000, step=500, value=3000, label="Máx. passos/simulação")
    beam_w = mo.ui.slider(8, 128, step=8, value=32, label="Largura do feixe")
    mo.hstack([analysis_btn, n_runs, sim_steps, beam_w], justify="start", wrap=True)
    return analysis_btn, beam_w, n_runs, sim_steps


@app.cell
def _(
    MODO_SINCRONO,
    N,
    analyse_sync,
    analysis_btn,
    async_random_runs,
    beam_search_error,
    beam_w,
    border,
    fmt_cells,
    mask_to_cells,
    mo,
    mode,
    n_runs,
    only_unstable,
    seed,
    sim_steps,
):
    mo.stop(
        not analysis_btn.value,
        mo.md("_Prima **Analisar propriedades** para correr a análise._"),
    )

    if mode == MODO_SINCRONO:
        _r = analyse_sync(N, border)
        if not _r["cycle_found"]:
            _txt = (
                f"### Modo síncrono (N={N}, semente={seed})\n\n"
                f"Não foi encontrado ciclo em {_r['steps']} passos → **inconclusivo**. "
                f"Erro visitado até aqui: {_r['error_t'] is not None}."
            )
        else:
            _dead = mask_to_cells(_r["perm_dead"])
            _alive = mask_to_cells(_r["perm_alive"])
            _p1 = (
                "✅ **Verdadeira** — o estado de erro nunca é visitado"
                if _r["error_t"] is None
                else f"❌ **Falsa** — estado de erro atingido em t = {_r['error_t']}"
            )
            _p2 = (
                "✅ **Verdadeira**"
                if not _dead and not _alive
                else "❌ **Falsa**"
            )
            _txt = f"""### Modo síncrono (N={N}, semente={seed}) — resultado exato

    Transiente: **{_r['transient']}** passos · período do ciclo: **{_r['period']}**

    * **(i)** {_p1}
    * **(ii)** {_p2}
        * permanentemente **mortas** (no ciclo): **{len(_dead)}** — {fmt_cells(_dead)}
        * permanentemente **vivas** (no ciclo): **{len(_alive)}** — {fmt_cells(_alive)}
    """
    else:
        _runs = async_random_runs(N, border, n_runs.value, sim_steps.value,
                                  only_unstable.value, seed)
        _beam = beam_search_error(N, border, beam=beam_w.value, seed=seed)
        _ex = _runs["fixed_example"]
        _fx = ""
        if _ex is not None:
            _d = mask_to_cells(~_ex)
            _a = mask_to_cells(_ex)
            _fx = (
                f"\n    * num ponto fixo atingido: **{len(_a)}** células permanentemente vivas e "
                f"**{len(_d)}** permanentemente mortas ⇒ **(ii) é falsa** (contra-exemplo)."
            )
        if _beam["found"]:
            _b = (
                f"❌ **(i) é falsa**: encontrado escalonamento com {len(_beam['path'])} "
                f"atualizações que atinge o estado de erro. Primeiras células a atualizar: "
                f"{fmt_cells(_beam['path'], 15)}"
            )
        else:
            _b = (
                f"Pesquisa em feixe **não** encontrou erro ({_beam['reason']}, "
                f"{_beam['explored']} estados explorados) → *inconclusivo*, não prova (i)."
            )
        _txt = f"""### Modo assíncrono (N={N}, semente={seed}) — evidência por refutação

    **Simulações aleatórias** ({n_runs.value} execuções, ≤ {sim_steps.value} passos):
    * atingiram o estado de erro: **{_runs['n_error']}**
    * terminaram num ponto fixo: **{_runs['n_fixed']}**
    * ainda em evolução no limite: **{_runs['n_open']}**{_fx}

    **Pesquisa de escalonamento até ao erro:** {_b}
    """
    mo.md(_txt)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ---
    ### Verificação exaustiva (apenas N pequeno)

    Constrói o grafo de estados alcançável **completo** para um $N$ pequeno (fora do requisito $N>16$,
    serve para validar o modelo) e verifica (i) por alcançabilidade e (ii) por
    $\mathbf{EF}\,\mathbf{EG}\,(c=v)$, ignorando *stuttering* (só transições que mudam o estado;
    um estado sem transições efetivas conta como ponto fixo). Usa o modo e a semente atuais.
    """)
    return


@app.cell
def _(mo):
    mc_N = mo.ui.dropdown({"N = 3": 3, "N = 4": 4}, value="N = 4", label="N da verificação")
    mc_btn = mo.ui.run_button(label="🧪 Verificar exaustivamente")
    mo.hstack([mc_N, mc_btn], justify="start")
    return mc_N, mc_btn


@app.cell
def _(
    explore_fsm,
    fmt_cells,
    make_border_values,
    mc_N,
    mc_btn,
    mo,
    mode,
    seed,
):
    mo.stop(not mc_btn.value, mo.md("_Prima **Verificar exaustivamente**._"))
    _n = mc_N.value
    _res = explore_fsm(_n, make_border_values(_n, seed), mode)
    if _res["truncated"]:
        _out = f"Grafo truncado ({_res['n_states']} estados) → inconclusivo."
    else:
        _p1 = (
            "❌ **Falsa** — o estado de erro é alcançável"
            if _res["error_reachable"]
            else "✅ **Verdadeira** — o estado de erro não é alcançável"
        )
        _ok2 = not _res["perm_dead"] and not _res["perm_alive"]
        _p2 = "✅ **Verdadeira**" if _ok2 else "❌ **Falsa**"
        _out = f"""**{mode}**, N={_n}, semente={seed}

    Estados alcançáveis: **{_res['n_states']}** · transições efetivas: {_res['n_transitions']} · pontos fixos: {_res['n_fixed_points']}

    * **(i)** {_p1}
    * **(ii)** {_p2}
        * células que *podem* ficar permanentemente mortas: {len(_res['perm_dead'])} — {fmt_cells(_res['perm_dead'])}
        * células que *podem* ficar permanentemente vivas: {len(_res['perm_alive'])} — {fmt_cells(_res['perm_alive'])}
    """
    mo.md(_out)
    return


if __name__ == "__main__":
    app.run()
