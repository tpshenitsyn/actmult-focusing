# Фокусирование для инфинитарной логики действий с мультиплексированием

[**FocusingComplete.lean**](FocusingComplete.lean) содержит доказательство теоремы о фокусировании из диссертации Тихона Пшеницына. Используется Lean **4.19.0** и только встроенная библиотека `Std`.

## Формулы и секвенции

Все определения находятся в пространстве имён `Focusing`.

| Формула | Lean |
| --- | --- |
| $p_i$ | `Formula.atom i` |
| $\mathbf0$, $\mathbf1$ | `Formula.zero`, `Formula.one` |
| $A\otimes B$ | `Formula.tensor A B` |
| $A\backslash B$, $B/A$ | `Formula.ldiv A B`, `Formula.rdiv B A` |
| $A\mathbin{\&}B$, $A\oplus B$ | `Formula.conj A B`, `Formula.disj A B` |
| $A^*$, $!A$ | `Formula.star A`, `Formula.bang A` |

```lean
abbrev Context := List Formula
abbrev Theory := Formula → Prop
```

Контекст — конечный упорядоченный список формул; пустой контекст разрешён. `[]` — пустой список, `A :: R` — добавление формулы в начало списка, `L ++ R` — конкатенация. В частности, `L ++ A :: R` обозначает контекст $L,A,R$. `List.replicate n A` — $n$ вхождений $A$, а `parts.flatten` — конкатенация списка контекстов.

`H : Theory` задаёт простое множество гипотез: `H A` означает $(\Rightarrow A)\in\mathcal H$. Отдельный тип обычных секвенций не вводится: секвенция задаётся контекстом и сукцедентом. **Выводимость обычной секвенции** $\Gamma\Rightarrow A$ из этих гипотез с произвольными сечениями записывается как `Ordinary H Γ A`. Это индуктивно определённое отношение: его конструкторы — аксиома и правила вывода.

**Фокусированная секвенция** — значение типа `Judgment`; её выводимость выражается утверждением `Focused H j`.

| Секвенция | Значение Lean | Сокращение в таблицах |
| --- | --- | --- |
| $L\Uparrow R\Rightarrow C\Uparrow\cdot$ | `Judgment.up L R C Side.active` | $U_a(L;R;C)$ |
| $L\Uparrow R\Rightarrow\cdot\Uparrow C$ | `Judgment.up L R C Side.stored` | $U_t(L;R;C)$ |
| $L\Downarrow A,R\Rightarrow\cdot\Downarrow C$ | `Judgment.left L A R C` | $L_f(L;A;R;C)$ |
| $\Gamma\Downarrow\cdot\Rightarrow A\Downarrow\cdot$ | `Judgment.right Γ A` | $R_f(\Gamma;A)$ |

В левофокусированной секвенции фокус находится на указанном вхождении $A$, в правофокусированной — на сукцеденте. Точка обозначает пустой контекст. Индекс $s$ в $U_s$ означает любой из вариантов $a,t$.

Для краткости **только в таблицах типов** используются сокращения:

- `O Γ A` = `Ordinary H Γ A`;
- `U L R C s` = `Focused H (.up L R C s)`;
- `LF L A R C` = `Focused H (.left L A R C)`;
- `RF Γ A` = `Focused H (.right Γ A)`.

Имена `tensor`, `ldiv` и т. д. в типах — конструкторы `Formula`; `.active`, `.stored` — конструкторы `Side`. Параметры конструкторов правил опущены: $L,R,\Gamma,\Delta,\Xi$ — контексты, $A,B,C$ — формулы, `p : Nat`, `n : Nat`, `parts : List Context`. Стрелка `→` отделяет предпосылки от заключения.

## Обычное исчисление: `Ordinary`

| Правило | Математическая запись | Тип конструктора Lean |
| --- | --- | --- |
| `identity` | $\frac{}{p\Rightarrow p}$ | `O [atom p] (atom p)` |
| `tensorL` | $\frac{L,A,B,R\Rightarrow C}{L,A\otimes B,R\Rightarrow C}$ | `O (L ++ A :: B :: R) C → O (L ++ tensor A B :: R) C` |
| `tensorR` | $\frac{\Gamma\Rightarrow A\quad\Delta\Rightarrow B}{\Gamma,\Delta\Rightarrow A\otimes B}$ | `O Γ A → O Δ B → O (Γ ++ Δ) (tensor A B)` |
| `ldivL` | $\frac{L,B,R\Rightarrow C\quad\Xi\Rightarrow A}{L,\Xi,A\backslash B,R\Rightarrow C}$ | `O (L ++ B :: R) C → O Ξ A → O (L ++ Ξ ++ ldiv A B :: R) C` |
| `ldivR` | $\frac{A,\Gamma\Rightarrow B}{\Gamma\Rightarrow A\backslash B}$ | `O (A :: Γ) B → O Γ (ldiv A B)` |
| `rdivL` | $\frac{L,B,R\Rightarrow C\quad\Xi\Rightarrow A}{L,B/A,\Xi,R\Rightarrow C}$ | `O (L ++ B :: R) C → O Ξ A → O (L ++ rdiv B A :: (Ξ ++ R)) C` |
| `rdivR` | $\frac{\Gamma,A\Rightarrow B}{\Gamma\Rightarrow B/A}$ | `O (Γ ++ [A]) B → O Γ (rdiv B A)` |
| `zeroL` | $\frac{}{L,\mathbf0,R\Rightarrow C}$ | `O (L ++ zero :: R) C` |
| `oneL` | $\frac{L,R\Rightarrow C}{L,\mathbf1,R\Rightarrow C}$ | `O (L ++ R) C → O (L ++ one :: R) C` |
| `oneR` | $\frac{}{\Rightarrow\mathbf1}$ | `O [] one` |
| `conjL₁` | $\frac{L,A,R\Rightarrow C}{L,A\mathbin{\&}B,R\Rightarrow C}$ | `O (L ++ A :: R) C → O (L ++ conj A B :: R) C` |
| `conjL₂` | $\frac{L,B,R\Rightarrow C}{L,A\mathbin{\&}B,R\Rightarrow C}$ | `O (L ++ B :: R) C → O (L ++ conj A B :: R) C` |
| `conjR` | $\frac{\Gamma\Rightarrow A\quad\Gamma\Rightarrow B}{\Gamma\Rightarrow A\mathbin{\&}B}$ | `O Γ A → O Γ B → O Γ (conj A B)` |
| `disjL` | $\frac{L,A,R\Rightarrow C\quad L,B,R\Rightarrow C}{L,A\oplus B,R\Rightarrow C}$ | `O (L ++ A :: R) C → O (L ++ B :: R) C → O (L ++ disj A B :: R) C` |
| `disjR₁` | $\frac{\Gamma\Rightarrow A}{\Gamma\Rightarrow A\oplus B}$ | `O Γ A → O Γ (disj A B)` |
| `disjR₂` | $\frac{\Gamma\Rightarrow B}{\Gamma\Rightarrow A\oplus B}$ | `O Γ B → O Γ (disj A B)` |
| `starL` | $\frac{\{L,A^n,R\Rightarrow C\}_{n\in\mathbb N}}{L,A^*,R\Rightarrow C}$ | `(∀ n : Nat, O (L ++ List.replicate n A ++ R) C) → O (L ++ star A :: R) C` |
| `starR` | $\frac{\Gamma_1\Rightarrow A\quad\cdots\quad\Gamma_n\Rightarrow A}{\Gamma_1,\ldots,\Gamma_n\Rightarrow A^*}$ | `(∀ Γ ∈ parts, O Γ A) → O parts.flatten (star A)` |
| `bangL` | $\frac{L,A^n,R\Rightarrow C}{L,!A,R\Rightarrow C}$ | `O (L ++ List.replicate n A ++ R) C → O (L ++ bang A :: R) C` |
| `bangR` | $\frac{A\Rightarrow B}{!A\Rightarrow !B}$ | `O [A] B → O [bang A] (bang B)` |
| `hypothesis` | $\frac{(\Rightarrow A)\in\mathcal H}{\Rightarrow A}$ | `H A → O [] A` |
| `cut` | $\frac{\Xi\Rightarrow A\quad L,A,R\Rightarrow C}{L,\Xi,R\Rightarrow C}$ | `O Ξ A → O (L ++ A :: R) C → O (L ++ Ξ ++ R) C` |

## Фокусированное исчисление: `Focused`

Пусть $P$ — позитивные формулы ($\mathbf0,\mathbf1,A\otimes B,A\oplus B,A^*$), $N$ — негативные ($A\backslash B,B/A,A\mathbin{\&}B$), $M$ — формулы $!A$, $V$ — переменные. В Lean этим условиям соответствуют `positive`, `negative`, `rightRelease` ($N\cup M$) и `rightSync` ($P\cup V$).

| Правило | Математическая запись | Тип конструктора Lean |
| --- | --- | --- |
| `identity` | $\frac{}{R_f(p;p)}$ | `RF [atom p] (atom p)` |
| `tensorL` | $\frac{U_s(L;A,B,R;C)}{U_s(L;A\otimes B,R;C)}$ | `U L (A :: B :: R) C s → U L (tensor A B :: R) C s` |
| `ldivR` | $\frac{U_a(\cdot;A,\Gamma;B)}{U_a(\Gamma;\cdot;A\backslash B)}$ | `U [] (A :: Γ) B .active → U Γ [] (ldiv A B) .active` |
| `rdivR` | $\frac{U_a(\Gamma;A;B)}{U_a(\Gamma;\cdot;B/A)}$ | `U Γ [A] B .active → U Γ [] (rdiv B A) .active` |
| `zeroL` | $\frac{}{U_s(L;\mathbf0,R;C)}$ | `U L (zero :: R) C s` |
| `oneL` | $\frac{U_s(L;R;C)}{U_s(L;\mathbf1,R;C)}$ | `U L R C s → U L (one :: R) C s` |
| `disjL` | $\frac{U_s(L;A,R;C)\quad U_s(L;B,R;C)}{U_s(L;A\oplus B,R;C)}$ | `U L (A :: R) C s → U L (B :: R) C s → U L (disj A B :: R) C s` |
| `conjR` | $\frac{U_a(\Gamma;\cdot;A)\quad U_a(\Gamma;\cdot;B)}{U_a(\Gamma;\cdot;A\mathbin{\&}B)}$ | `U Γ [] A .active → U Γ [] B .active → U Γ [] (conj A B) .active` |
| `starL` | $\frac{\{U_s(L;A^n,R;C)\}_{n\in\mathbb N}}{U_s(L;A^*,R;C)}$ | `(∀ n : Nat, U L (List.replicate n A ++ R) C s) → U L (star A :: R) C s` |
| `tensorR` | $\frac{R_f(\Gamma;A)\quad R_f(\Delta;B)}{R_f(\Gamma,\Delta;A\otimes B)}$ | `RF Γ A → RF Δ B → RF (Γ ++ Δ) (tensor A B)` |
| `ldivL` | $\frac{L_f(L;B;R;C)\quad R_f(\Xi;A)}{L_f(L,\Xi;A\backslash B;R;C)}$ | `LF L B R C → RF Ξ A → LF (L ++ Ξ) (ldiv A B) R C` |
| `rdivL` | $\frac{L_f(L;B;R;C)\quad R_f(\Xi;A)}{L_f(L;B/A;\Xi,R;C)}$ | `LF L B R C → RF Ξ A → LF L (rdiv B A) (Ξ ++ R) C` |
| `oneR` | $\frac{}{R_f(\cdot;\mathbf1)}$ | `RF [] one` |
| `conjL₁` | $\frac{L_f(L;A;R;C)}{L_f(L;A\mathbin{\&}B;R;C)}$ | `LF L A R C → LF L (conj A B) R C` |
| `conjL₂` | $\frac{L_f(L;B;R;C)}{L_f(L;A\mathbin{\&}B;R;C)}$ | `LF L B R C → LF L (conj A B) R C` |
| `disjR₁` | $\frac{R_f(\Gamma;A)}{R_f(\Gamma;A\oplus B)}$ | `RF Γ A → RF Γ (disj A B)` |
| `disjR₂` | $\frac{R_f(\Gamma;B)}{R_f(\Gamma;A\oplus B)}$ | `RF Γ B → RF Γ (disj A B)` |
| `starR` | $\frac{R_f(\Gamma_1;A)\quad\cdots\quad R_f(\Gamma_n;A)}{R_f(\Gamma_1,\ldots,\Gamma_n;A^*)}$ | `(∀ Γ ∈ parts, RF Γ A) → RF parts.flatten (star A)` |
| `bangL` | $\frac{U_t(L;A^n,R;C)}{U_t(L,!A,R;\cdot;C)}$ | `U L (List.replicate n A ++ R) C .stored → U (L ++ bang A :: R) [] C .stored` |
| `bangR` | $\frac{U_a(\cdot;A;B)}{U_t(!A;\cdot;!B)}$ | `U [] [A] B .active → U [bang A] [] (bang B) .stored` |
| `releaseL` | $\frac{U_t(L;A,R;C)}{L_f(L;A;R;C)}\quad(A\notin N)$ | `A.negative = false → U L (A :: R) C .stored → LF L A R C` |
| `releaseR` | $\frac{U_a(\Gamma;\cdot;A)}{R_f(\Gamma;A)}\quad(A\in N\cup M)$ | `A.rightRelease = true → U Γ [] A .active → RF Γ A` |
| `storeL` | $\frac{U_s(L,A;R;C)}{U_s(L;A,R;C)}\quad(A\notin P)$ | `A.positive = false → U (L ++ [A]) R C s → U L (A :: R) C s` |
| `storeR` | $\frac{U_t(\Gamma;\cdot;A)}{U_a(\Gamma;\cdot;A)}\quad(A\notin N)$ | `A.negative = false → U Γ [] A .stored → U Γ [] A .active` |
| `decideL` | $\frac{L_f(L;A;R;C)}{U_t(L,A,R;\cdot;C)}\quad(A\in N)$ | `A.negative = true → LF L A R C → U (L ++ A :: R) [] C .stored` |
| `decideR` | $\frac{R_f(\Gamma;A)}{U_t(\Gamma;\cdot;A)}\quad(A\in P\cup V)$ | `A.rightSync = true → RF Γ A → U Γ [] A .stored` |
| `decideH` | $\frac{L_f(L;A;R;C)}{U_t(L,R;\cdot;C)}\quad((\Rightarrow A)\in\mathcal H)$ | `H A → LF L A R C → U (L ++ R) [] C .stored` |

В обоих исчислениях `starL` имеет **счётно бесконечное** семейство посылок: `∀ n : Nat, ...`. Правило `starR` имеет конечное число посылок, заданное списком `parts`; пустой список разрешён. В `bangL` также разрешено `n = 0`.

## Основная теорема

Для любого простого множества гипотез $\mathcal H$:

$$
\mathcal H\vdash^{\mathrm{cut}}_{!^m\mathrm{ACT}_\omega}\Gamma\Rightarrow A
\quad\Longleftrightarrow\quad
\vdash_{!^m\mathrm{ACT}_\omega^{\mathrm{foc}}+\mathcal H}
\cdot\Uparrow\Gamma\Rightarrow A\Uparrow\cdot
$$

Начальная разметка и доказанная теорема записаны в Lean так:

```lean
def foc (Γ : Context) (A : Formula) : Judgment :=
  .up [] Γ A .active

theorem focusing {H : Theory} {Γ A} :
    Ordinary H Γ A ↔ Focused H (foc Γ A) :=
  ⟨focusing_complete, focused_sound⟩
```

Полное имя теоремы — `Focusing.focusing`. Нормализация сечения и необходимые леммы о фокусировании доказаны в том же файле.

## Проверка

После установки [Lean](https://lean-lang.org/install/) выполните в каталоге репозитория:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
```

`Audit.lean` проверяет формулировку основной теоремы и зависимости от аксиом; ожидаются только стандартные `propext` и `Quot.sound`, без `sorryAx`. Эти проверки также запускаются в GitHub Actions.

Автор математического результата — **Тихон Пшеницын**. Формализация подготовлена при существенной помощи OpenAI ChatGPT.
