# Фокусирование для инфинитарной логики действий с мультиплексированием

[**FocusingComplete.lean**](FocusingComplete.lean) содержит доказательство теоремы о фокусировании из диссертации Тихона Пшеницына. Используется Lean **4.19.0** и только стандартная библиотека `Std`, поставляемая с Lean; дополнительных математических библиотек нет. Автор математического результата — Тихон Пшеницын; формализация подготовлена при существенной помощи OpenAI ChatGPT.

## 1. Формулы и секвенции

Все определения находятся в пространстве имён `Focusing`. **Часть I файла, строки 14–171, содержит определения, необходимые для формулировки основной теоремы, и заканчивается её точной записью в комментарии.** Вспомогательные определения и доказательства начинаются в части II. Поэтому для проверки того, *какое именно утверждение доказано*, достаточно сопоставить часть I с объявлением `theorem focusing` в конце доказательства. Ссылки на номера строк ниже закреплены за версией Lean-файла, использованной при подготовке этого README.

### Формулы

$`A,B ::= p_i\mid\mathbf{0}\mid\mathbf{1}\mid A\otimes B\mid A\backslash B\mid B/A\mid A\mathbin{\And}B\mid A\oplus B\mid A^*\mid !A`$

[L14–L25](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L14-L25)

```lean
inductive Formula where
  | atom : Nat → Formula
  | zero : Formula
  | one : Formula
  | tensor : Formula → Formula → Formula
  | ldiv : Formula → Formula → Formula
  | rdiv : Formula → Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | star : Formula → Formula
  | bang : Formula → Formula
  deriving DecidableEq, Repr
```

`atom i` обозначает $`p_i`$; `zero`, `one` — $`\mathbf{0},\mathbf{1}`$; `tensor`, `ldiv`, `rdiv`, `conj`, `disj`, `star`, `bang` соответствуют связкам в указанном порядке. В частности, `rdiv B A` — $`B/A`$. `deriving DecidableEq, Repr` автоматически добавляет проверку равенства и текстовое представление формул; логических правил эта строка не добавляет.

### Контексты, гипотезы и обычные секвенции

[L27–L28](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L27-L28)

```lean
abbrev Context := List Formula
abbrev Theory := Formula → Prop
```

Контекст — конечная **упорядоченная** последовательность формул; пустой контекст разрешён. `[]` — пустой список, `A :: R` добавляет `A` в начало `R`, а `L ++ R` соединяет списки. Поэтому `L ++ A :: R` означает $`L,A,R`$. `List.replicate n A` — $`n`$ вхождений $`A`$; `parts.flatten` соединяет конечный список контекстов. В математической записи $`A^n`$ означает последовательность из $`n`$ вхождений $`A`$, а точка — пустую последовательность.

`H : Theory` представляет простое множество гипотез: `H A` означает $`(\Rightarrow A)\in\mathcal H`$. Отдельного типа обычных секвенций нет: секвенция задаётся контекстом и сукцедентом. Утверждение `Ordinary H Γ A` означает выводимость $`\Gamma\Rightarrow A`$ из этих гипотез с произвольными сечениями. Отношение выводимости объявлено так; все его конструкторы приведены в разделе 2:

[L69](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L69)

```lean
inductive Ordinary (H : Theory) : Context → Formula → Prop where
```

### Фокусированные секвенции

[L51–L61](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L51-L61)

```lean
inductive Side where
  | active
  | stored
  deriving DecidableEq, Repr

/-- A left focused judgment includes its focused formula separately. -/
inductive Judgment where
  | up : Context → Context → Formula → Side → Judgment
  | left : Context → Formula → Context → Formula → Judgment
  | right : Context → Formula → Judgment
  deriving DecidableEq, Repr
```

Здесь `Side` задаёт положение сукцедента в отрицательной фазе. Четырём вариантам секвенций соответствуют следующие значения `Judgment`:

- `Judgment.up L R C .active` — $`L\Uparrow R\Rightarrow C\Uparrow\cdot`$;
- `Judgment.up L R C .stored` — $`L\Uparrow R\Rightarrow\cdot\Uparrow C`$;
- `Judgment.left L A R C` — $`L\Downarrow A,R\Rightarrow\cdot\Downarrow C`$;
- `Judgment.right Γ A` — $`\Gamma\Downarrow\cdot\Rightarrow A\Downarrow\cdot`$.

В левофокусированной секвенции выделено указанное вхождение $`A`$, в правофокусированной — сукцедент. Выводимость `j : Judgment` записывается `Focused H j`.

### Контекст и сукцедент без разметки

Функции `Judgment.context` и `Judgment.succedent` из части II стирают разметку секвенции. Они используются в доказательстве и не входят в формулировку основной теоремы:

[L189–L195](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L189-L195)

```lean
def context : Judgment → Context
  | .up L R _ _ => L ++ R
  | .left L A R _ => L ++ A :: R
  | .right Γ _ => Γ

def succedent : Judgment → Formula
  | .up _ _ C _ | .left _ _ _ C | .right _ C => C
```

## 2. Правила обычного исчисления

В первом столбце посылки стоят над чертой, заключение — под ней; во втором приведены **полные строки исходного кода**, включая параметры конструктора. Стрелка `→` отделяет предпосылки от заключения; параметры в `{…}` Lean восстанавливает из контекста. Начальный знак `|` перечисляет конструкторы одного индуктивного определения. В этих правилах все секвенции рассматриваются при одном и том же множестве гипотез $`\mathcal H`$.

| Математическая запись | Полный конструктор Lean |
| :--- | :--- |
| **`identity`**<br>$`\displaystyle \frac{}{p\Rightarrow p}`$ | [L70](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L70)<br><code>  &#124; identity (p) : Ordinary H [atom p] (atom p)</code> |
| **`tensorL`**<br>$`\displaystyle \frac{L,A,B,R\Rightarrow C}{L,A\otimes B,R\Rightarrow C}`$ | [L71–L72](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L71-L72)<br><code>  &#124; tensorL {L R A B C} : Ordinary H (L ++ A :: B :: R) C →</code><br><code>      Ordinary H (L ++ tensor A B :: R) C</code> |
| **`tensorR`**<br>$`\displaystyle \frac{\Gamma\Rightarrow A\quad\Delta\Rightarrow B}{\Gamma,\Delta\Rightarrow A\otimes B}`$ | [L73–L74](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L73-L74)<br><code>  &#124; tensorR {Γ Δ A B} : Ordinary H Γ A → Ordinary H Δ B →</code><br><code>      Ordinary H (Γ ++ Δ) (tensor A B)</code> |
| **`ldivL`**<br>$`\displaystyle \frac{L,B,R\Rightarrow C\quad\Xi\Rightarrow A}{L,\Xi,A\backslash B,R\Rightarrow C}`$ | [L75–L76](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L75-L76)<br><code>  &#124; ldivL {L Ξ R A B C} : Ordinary H (L ++ B :: R) C →</code><br><code>      Ordinary H Ξ A → Ordinary H (L ++ Ξ ++ ldiv A B :: R) C</code> |
| **`ldivR`**<br>$`\displaystyle \frac{A,\Gamma\Rightarrow B}{\Gamma\Rightarrow A\backslash B}`$ | [L77](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L77)<br><code>  &#124; ldivR {Γ A B} : Ordinary H (A :: Γ) B → Ordinary H Γ (ldiv A B)</code> |
| **`rdivL`**<br>$`\displaystyle \frac{L,B,R\Rightarrow C\quad\Xi\Rightarrow A}{L,B/A,\Xi,R\Rightarrow C}`$ | [L78–L79](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L78-L79)<br><code>  &#124; rdivL {L Ξ R A B C} : Ordinary H (L ++ B :: R) C →</code><br><code>      Ordinary H Ξ A → Ordinary H (L ++ rdiv B A :: (Ξ ++ R)) C</code> |
| **`rdivR`**<br>$`\displaystyle \frac{\Gamma,A\Rightarrow B}{\Gamma\Rightarrow B/A}`$ | [L80](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L80)<br><code>  &#124; rdivR {Γ A B} : Ordinary H (Γ ++ [A]) B → Ordinary H Γ (rdiv B A)</code> |
| **`zeroL`**<br>$`\displaystyle \frac{}{L,\mathbf{0},R\Rightarrow C}`$ | [L81](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L81)<br><code>  &#124; zeroL (L R C) : Ordinary H (L ++ zero :: R) C</code> |
| **`oneL`**<br>$`\displaystyle \frac{L,R\Rightarrow C}{L,\mathbf{1},R\Rightarrow C}`$ | [L82](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L82)<br><code>  &#124; oneL {L R C} : Ordinary H (L ++ R) C → Ordinary H (L ++ one :: R) C</code> |
| **`oneR`**<br>$`\displaystyle \frac{}{\Rightarrow\mathbf{1}}`$ | [L83](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L83)<br><code>  &#124; oneR : Ordinary H [] one</code> |
| **`conjL₁`**<br>$`\displaystyle \frac{L,A,R\Rightarrow C}{L,A\mathbin{\And}B,R\Rightarrow C}`$ | [L84–L85](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L84-L85)<br><code>  &#124; conjL₁ {L R A B C} : Ordinary H (L ++ A :: R) C →</code><br><code>      Ordinary H (L ++ conj A B :: R) C</code> |
| **`conjL₂`**<br>$`\displaystyle \frac{L,B,R\Rightarrow C}{L,A\mathbin{\And}B,R\Rightarrow C}`$ | [L86–L87](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L86-L87)<br><code>  &#124; conjL₂ {L R A B C} : Ordinary H (L ++ B :: R) C →</code><br><code>      Ordinary H (L ++ conj A B :: R) C</code> |
| **`conjR`**<br>$`\displaystyle \frac{\Gamma\Rightarrow A\quad\Gamma\Rightarrow B}{\Gamma\Rightarrow A\mathbin{\And}B}`$ | [L88–L89](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L88-L89)<br><code>  &#124; conjR {Γ A B} : Ordinary H Γ A → Ordinary H Γ B →</code><br><code>      Ordinary H Γ (conj A B)</code> |
| **`disjL`**<br>$`\displaystyle \frac{L,A,R\Rightarrow C\quad L,B,R\Rightarrow C}{L,A\oplus B,R\Rightarrow C}`$ | [L90–L91](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L90-L91)<br><code>  &#124; disjL {L R A B C} : Ordinary H (L ++ A :: R) C →</code><br><code>      Ordinary H (L ++ B :: R) C → Ordinary H (L ++ disj A B :: R) C</code> |
| **`disjR₁`**<br>$`\displaystyle \frac{\Gamma\Rightarrow A}{\Gamma\Rightarrow A\oplus B}`$ | [L92](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L92)<br><code>  &#124; disjR₁ {Γ A B} : Ordinary H Γ A → Ordinary H Γ (disj A B)</code> |
| **`disjR₂`**<br>$`\displaystyle \frac{\Gamma\Rightarrow B}{\Gamma\Rightarrow A\oplus B}`$ | [L93](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L93)<br><code>  &#124; disjR₂ {Γ A B} : Ordinary H Γ B → Ordinary H Γ (disj A B)</code> |
| **`starL`**<br>$`\displaystyle \frac{\{L,A^n,R\Rightarrow C\}_{n\in\mathbb N}}{L,A^*,R\Rightarrow C}`$ | [L94–L96](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L94-L96)<br><code>  &#124; starL {L R A C} :</code><br><code>      (∀ n : Nat, Ordinary H (L ++ List.replicate n A ++ R) C) →</code><br><code>      Ordinary H (L ++ star A :: R) C</code> |
| **`starR`**<br>$`\displaystyle \frac{\Gamma_1\Rightarrow A\quad\cdots\quad\Gamma_n\Rightarrow A}{\Gamma_1,\ldots,\Gamma_n\Rightarrow A^*}`$ | [L97–L98](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L97-L98)<br><code>  &#124; starR {A} (parts : List Context) :</code><br><code>      (∀ Γ ∈ parts, Ordinary H Γ A) → Ordinary H parts.flatten (star A)</code> |
| **`bangL`**<br>$`\displaystyle \frac{L,A^n,R\Rightarrow C}{L,!A,R\Rightarrow C}`$ | [L99–L101](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L99-L101)<br><code>  &#124; bangL {L R A C} (n : Nat) :</code><br><code>      Ordinary H (L ++ List.replicate n A ++ R) C →</code><br><code>      Ordinary H (L ++ bang A :: R) C</code> |
| **`bangR`**<br>$`\displaystyle \frac{A\Rightarrow B}{!A\Rightarrow !B}`$ | [L102](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L102)<br><code>  &#124; bangR {A B} : Ordinary H [A] B → Ordinary H [bang A] (bang B)</code> |
| **`hypothesis`**<br>$`\displaystyle \frac{(\Rightarrow A)\in\mathcal H}{\Rightarrow A}`$ | [L103](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L103)<br><code>  &#124; hypothesis {A} : H A → Ordinary H [] A</code> |
| **`cut`**<br>$`\displaystyle \frac{\Xi\Rightarrow A\quad L,A,R\Rightarrow C}{L,\Xi,R\Rightarrow C}`$ | [L104–L105](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L104-L105)<br><code>  &#124; cut {L R Ξ A C} : Ordinary H Ξ A → Ordinary H (L ++ A :: R) C →</code><br><code>      Ordinary H (L ++ Ξ ++ R) C</code> |

В `starL` посылки заданы для **всех** `n : Nat`, то есть их счётно бесконечно. В `starR` список `parts` конечен; при `parts = []` получается аксиома $`\Rightarrow A^*`$. В `bangL` также разрешено `n = 0`. `hypothesis` вводит гипотезу из $`\mathcal H`$, а `cut` — произвольное сечение.

## 3. Определения для фокусирования

Позитивные формулы $`P`$ имеют вид $`\mathbf{0},\mathbf{1},A\otimes B,A\oplus B,A^*`$; негативные $`N`$ — $`A\backslash B,B/A,A\mathbin{\And}B`$. Обозначим через $`M`$ формулы $`!A`$, через $`V`$ — переменные. Принадлежность этим классам определяется по внешней связке. Булевы функции `rightSync` и `rightRelease` распознают соответственно $`P\cup V`$ и $`N\cup M`$:

[L32–L46](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L32-L46)

```lean
def positive : Formula → Bool
  | .zero | .one | .tensor _ _ | .disj _ _ | .star _ => true
  | _ => false

def negative : Formula → Bool
  | .ldiv _ _ | .rdiv _ _ | .conj _ _ => true
  | _ => false

def rightSync : Formula → Bool
  | .atom _ | .zero | .one | .tensor _ _ | .disj _ _ | .star _ => true
  | _ => false

def rightRelease : Formula → Bool
  | .ldiv _ _ | .rdiv _ _ | .conj _ _ | .bang _ => true
  | _ => false
```

Эти четыре функции определены в пространстве имён `Formula`, поэтому, например, `A.negative` означает `Formula.negative A`. Начальная разметка обычной секвенции задаётся функцией `foc`:

[L63–L64](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L63-L64)

```lean
def foc (Γ : Context) (A : Formula) : Judgment :=
  .up [] Γ A .active
```

Таким образом, `foc Γ A` — ровно $`\cdot\Uparrow\Gamma\Rightarrow A\Uparrow\cdot`$. Никаких дополнительных условий на формулы или гипотезы эта функция не накладывает.

<details>
<summary>Служебная разметка внутри доказательства</summary>

`split` разбивает контекст перед первой позитивной формулой; `canonical` использует это разбиение и выбирает положение сукцедента. Это вспомогательные определения части II: в основной теореме используется `foc`, а не `canonical`.

[L200–L207](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L200-L207)

```lean
def split : Context → Context × Context
  | [] => ([], [])
  | A :: Γ => if A.positive then ([], A :: Γ)
              else let p := split Γ; (A :: p.1, p.2)

def canonical (Γ : Context) (A : Formula) : Judgment :=
  let p := split Γ
  .up p.1 p.2 A (if A.negative then .active else .stored)
```

</details>

## 4. Правила фокусированного исчисления

[L109](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L109)

```lean
inductive Focused (H : Theory) : Judgment → Prop where
```

В правилах отрицательной фазы $`\Omega_s(C)`$ означает $`C\Uparrow\cdot`$ при `s = .active` и $`\cdot\Uparrow C`$ при `s = .stored`. Это сокращение используется только для сукцедента в математическом столбце; код Lean приведён без сокращений. На пассивные части контекста дополнительных ограничений не накладывается.

### Аксиома

| Математическая запись | Полный конструктор Lean |
| :--- | :--- |
| **`identity`**<br>$`\displaystyle \frac{}{p\Downarrow\cdot\Rightarrow p\Downarrow\cdot}`$ | [L110](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L110)<br><code>  &#124; identity (p) : Focused H (.right [atom p] (atom p))</code> |

### Отрицательная фаза

| Математическая запись | Полный конструктор Lean |
| :--- | :--- |
| **`tensorL`**<br>$`\displaystyle \frac{L\Uparrow A,B,R\Rightarrow \Omega_s(C)}{L\Uparrow A\otimes B,R\Rightarrow \Omega_s(C)}`$ | [L111–L112](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L111-L112)<br><code>  &#124; tensorL {L R A B C s} : Focused H (.up L (A :: B :: R) C s) →</code><br><code>      Focused H (.up L (tensor A B :: R) C s)</code> |
| **`ldivR`**<br>$`\displaystyle \frac{\cdot\Uparrow A,\Gamma\Rightarrow B\Uparrow\cdot}{\Gamma\Uparrow \cdot\Rightarrow A\backslash B\Uparrow\cdot}`$ | [L113–L114](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L113-L114)<br><code>  &#124; ldivR {Γ A B} : Focused H (.up [] (A :: Γ) B .active) →</code><br><code>      Focused H (.up Γ [] (ldiv A B) .active)</code> |
| **`rdivR`**<br>$`\displaystyle \frac{\Gamma\Uparrow A\Rightarrow B\Uparrow\cdot}{\Gamma\Uparrow \cdot\Rightarrow B/A\Uparrow\cdot}`$ | [L115–L116](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L115-L116)<br><code>  &#124; rdivR {Γ A B} : Focused H (.up Γ [A] B .active) →</code><br><code>      Focused H (.up Γ [] (rdiv B A) .active)</code> |
| **`zeroL`**<br>$`\displaystyle \frac{}{L\Uparrow \mathbf{0},R\Rightarrow \Omega_s(C)}`$ | [L117](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L117)<br><code>  &#124; zeroL (L R C s) : Focused H (.up L (zero :: R) C s)</code> |
| **`oneL`**<br>$`\displaystyle \frac{L\Uparrow R\Rightarrow \Omega_s(C)}{L\Uparrow \mathbf{1},R\Rightarrow \Omega_s(C)}`$ | [L118–L119](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L118-L119)<br><code>  &#124; oneL {L R C s} : Focused H (.up L R C s) →</code><br><code>      Focused H (.up L (one :: R) C s)</code> |
| **`disjL`**<br>$`\displaystyle \frac{L\Uparrow A,R\Rightarrow \Omega_s(C)\quad L\Uparrow B,R\Rightarrow \Omega_s(C)}{L\Uparrow A\oplus B,R\Rightarrow \Omega_s(C)}`$ | [L120–L122](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L120-L122)<br><code>  &#124; disjL {L R A B C s} : Focused H (.up L (A :: R) C s) →</code><br><code>      Focused H (.up L (B :: R) C s) →</code><br><code>      Focused H (.up L (disj A B :: R) C s)</code> |
| **`conjR`**<br>$`\displaystyle \frac{\Gamma\Uparrow \cdot\Rightarrow A\Uparrow\cdot\quad \Gamma\Uparrow \cdot\Rightarrow B\Uparrow\cdot}{\Gamma\Uparrow \cdot\Rightarrow A\mathbin{\And}B\Uparrow\cdot}`$ | [L123–L124](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L123-L124)<br><code>  &#124; conjR {Γ A B} : Focused H (.up Γ [] A .active) →</code><br><code>      Focused H (.up Γ [] B .active) → Focused H (.up Γ [] (conj A B) .active)</code> |
| **`starL`**<br>$`\displaystyle \frac{\{L\Uparrow A^n,R\Rightarrow \Omega_s(C)\}_{n\in\mathbb N}}{L\Uparrow A^*,R\Rightarrow \Omega_s(C)}`$ | [L125–L127](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L125-L127)<br><code>  &#124; starL {L R A C s} :</code><br><code>      (∀ n : Nat, Focused H (.up L (List.replicate n A ++ R) C s)) →</code><br><code>      Focused H (.up L (star A :: R) C s)</code> |

### Положительная фаза

| Математическая запись | Полный конструктор Lean |
| :--- | :--- |
| **`tensorR`**<br>$`\displaystyle \frac{\Gamma\Downarrow\cdot\Rightarrow A\Downarrow\cdot\quad \Delta\Downarrow\cdot\Rightarrow B\Downarrow\cdot}{\Gamma,\Delta\Downarrow\cdot\Rightarrow A\otimes B\Downarrow\cdot}`$ | [L128–L129](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L128-L129)<br><code>  &#124; tensorR {Γ Δ A B} : Focused H (.right Γ A) → Focused H (.right Δ B) →</code><br><code>      Focused H (.right (Γ ++ Δ) (tensor A B))</code> |
| **`ldivL`**<br>$`\displaystyle \frac{L\Downarrow B,R\Rightarrow\cdot\Downarrow C\quad \Xi\Downarrow\cdot\Rightarrow A\Downarrow\cdot}{L,\Xi\Downarrow A\backslash B,R\Rightarrow\cdot\Downarrow C}`$ | [L130–L131](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L130-L131)<br><code>  &#124; ldivL {L Ξ R A B C} : Focused H (.left L B R C) →</code><br><code>      Focused H (.right Ξ A) → Focused H (.left (L ++ Ξ) (ldiv A B) R C)</code> |
| **`rdivL`**<br>$`\displaystyle \frac{L\Downarrow B,R\Rightarrow\cdot\Downarrow C\quad \Xi\Downarrow\cdot\Rightarrow A\Downarrow\cdot}{L\Downarrow B/A,\Xi,R\Rightarrow\cdot\Downarrow C}`$ | [L132–L133](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L132-L133)<br><code>  &#124; rdivL {L Ξ R A B C} : Focused H (.left L B R C) →</code><br><code>      Focused H (.right Ξ A) → Focused H (.left L (rdiv B A) (Ξ ++ R) C)</code> |
| **`oneR`**<br>$`\displaystyle \frac{}{\cdot\Downarrow\cdot\Rightarrow \mathbf{1}\Downarrow\cdot}`$ | [L134](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L134)<br><code>  &#124; oneR : Focused H (.right [] one)</code> |
| **`conjL₁`**<br>$`\displaystyle \frac{L\Downarrow A,R\Rightarrow\cdot\Downarrow C}{L\Downarrow A\mathbin{\And}B,R\Rightarrow\cdot\Downarrow C}`$ | [L135–L136](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L135-L136)<br><code>  &#124; conjL₁ {L R A B C} : Focused H (.left L A R C) →</code><br><code>      Focused H (.left L (conj A B) R C)</code> |
| **`conjL₂`**<br>$`\displaystyle \frac{L\Downarrow B,R\Rightarrow\cdot\Downarrow C}{L\Downarrow A\mathbin{\And}B,R\Rightarrow\cdot\Downarrow C}`$ | [L137–L138](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L137-L138)<br><code>  &#124; conjL₂ {L R A B C} : Focused H (.left L B R C) →</code><br><code>      Focused H (.left L (conj A B) R C)</code> |
| **`disjR₁`**<br>$`\displaystyle \frac{\Gamma\Downarrow\cdot\Rightarrow A\Downarrow\cdot}{\Gamma\Downarrow\cdot\Rightarrow A\oplus B\Downarrow\cdot}`$ | [L139](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L139)<br><code>  &#124; disjR₁ {Γ A B} : Focused H (.right Γ A) → Focused H (.right Γ (disj A B))</code> |
| **`disjR₂`**<br>$`\displaystyle \frac{\Gamma\Downarrow\cdot\Rightarrow B\Downarrow\cdot}{\Gamma\Downarrow\cdot\Rightarrow A\oplus B\Downarrow\cdot}`$ | [L140](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L140)<br><code>  &#124; disjR₂ {Γ A B} : Focused H (.right Γ B) → Focused H (.right Γ (disj A B))</code> |
| **`starR`**<br>$`\displaystyle \frac{\Gamma_1\Downarrow\cdot\Rightarrow A\Downarrow\cdot\quad\cdots\quad \Gamma_n\Downarrow\cdot\Rightarrow A\Downarrow\cdot}{\Gamma_1,\ldots,\Gamma_n\Downarrow\cdot\Rightarrow A^*\Downarrow\cdot}`$ | [L141–L142](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L141-L142)<br><code>  &#124; starR {A} (parts : List Context) :</code><br><code>      (∀ Γ ∈ parts, Focused H (.right Γ A)) → Focused H (.right parts.flatten (star A))</code> |

### Модальность мультиплексирования

| Математическая запись | Полный конструктор Lean |
| :--- | :--- |
| **`bangL`**<br>$`\displaystyle \frac{L\Uparrow A^n,R\Rightarrow \cdot\Uparrow C}{L,!A,R\Uparrow \cdot\Rightarrow \cdot\Uparrow C}`$ | [L143–L145](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L143-L145)<br><code>  &#124; bangL {L R A C} (n : Nat) :</code><br><code>      Focused H (.up L (List.replicate n A ++ R) C .stored) →</code><br><code>      Focused H (.up (L ++ bang A :: R) [] C .stored)</code> |
| **`bangR`**<br>$`\displaystyle \frac{\cdot\Uparrow A\Rightarrow B\Uparrow\cdot}{!A\Uparrow \cdot\Rightarrow \cdot\Uparrow !B}`$ | [L146–L147](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L146-L147)<br><code>  &#124; bangR {A B} : Focused H (.up [] [A] B .active) →</code><br><code>      Focused H (.up [bang A] [] (bang B) .stored)</code> |

### Решения и реакции

| Математическая запись | Полный конструктор Lean |
| :--- | :--- |
| **`releaseL`**<br>$`\displaystyle \frac{L\Uparrow A,R\Rightarrow \cdot\Uparrow C}{L\Downarrow A,R\Rightarrow\cdot\Downarrow C}\quad(A\notin N)`$ | [L148–L149](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L148-L149)<br><code>  &#124; releaseL {L R A C} : A.negative = false →</code><br><code>      Focused H (.up L (A :: R) C .stored) → Focused H (.left L A R C)</code> |
| **`releaseR`**<br>$`\displaystyle \frac{\Gamma\Uparrow \cdot\Rightarrow A\Uparrow\cdot}{\Gamma\Downarrow\cdot\Rightarrow A\Downarrow\cdot}\quad(A\in N\cup M)`$ | [L150–L151](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L150-L151)<br><code>  &#124; releaseR {Γ A} : A.rightRelease = true →</code><br><code>      Focused H (.up Γ [] A .active) → Focused H (.right Γ A)</code> |
| **`storeL`**<br>$`\displaystyle \frac{L,A\Uparrow R\Rightarrow \Omega_s(C)}{L\Uparrow A,R\Rightarrow \Omega_s(C)}\quad(A\notin P)`$ | [L152–L153](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L152-L153)<br><code>  &#124; storeL {L R A C s} : A.positive = false →</code><br><code>      Focused H (.up (L ++ [A]) R C s) → Focused H (.up L (A :: R) C s)</code> |
| **`storeR`**<br>$`\displaystyle \frac{\Gamma\Uparrow \cdot\Rightarrow \cdot\Uparrow A}{\Gamma\Uparrow \cdot\Rightarrow A\Uparrow\cdot}\quad(A\notin N)`$ | [L154–L155](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L154-L155)<br><code>  &#124; storeR {Γ A} : A.negative = false →</code><br><code>      Focused H (.up Γ [] A .stored) → Focused H (.up Γ [] A .active)</code> |
| **`decideL`**<br>$`\displaystyle \frac{L\Downarrow A,R\Rightarrow\cdot\Downarrow C}{L,A,R\Uparrow \cdot\Rightarrow \cdot\Uparrow C}\quad(A\in N)`$ | [L156–L157](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L156-L157)<br><code>  &#124; decideL {L R A C} : A.negative = true →</code><br><code>      Focused H (.left L A R C) → Focused H (.up (L ++ A :: R) [] C .stored)</code> |
| **`decideR`**<br>$`\displaystyle \frac{\Gamma\Downarrow\cdot\Rightarrow A\Downarrow\cdot}{\Gamma\Uparrow \cdot\Rightarrow \cdot\Uparrow A}\quad(A\in P\cup V)`$ | [L158–L159](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L158-L159)<br><code>  &#124; decideR {Γ A} : A.rightSync = true →</code><br><code>      Focused H (.right Γ A) → Focused H (.up Γ [] A .stored)</code> |
| **`decideH`**<br>$`\displaystyle \frac{L\Downarrow A,R\Rightarrow\cdot\Downarrow C}{L,R\Uparrow \cdot\Rightarrow \cdot\Uparrow C}\quad((\Rightarrow A)\in\mathcal H)`$ | [L160–L161](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L160-L161)<br><code>  &#124; decideH {L R A C} : H A →</code><br><code>      Focused H (.left L A R C) → Focused H (.up (L ++ R) [] C .stored)</code> |

В `starL`, `starR` и `bangL` соглашения о числе посылок те же, что в обычном исчислении. `decideH` соответствует гипотезе $`(\Rightarrow A)\in\mathcal H`$; произвольного сечения среди конструкторов `Focused` нет.

## 5. Основная теорема

Для любого простого множества гипотез $`\mathcal H`$, любого контекста $`\Gamma`$ и любой формулы $`A`$ равносильны выводимость обычной секвенции из гипотез с произвольными сечениями и выводимость её начальной разметки в фокусированном исчислении:

```math
\mathcal H\vdash^{\mathrm{cut}}_{!^{m}\mathrm{ACT}_{\omega}}\Gamma\Rightarrow A
\quad\Longleftrightarrow\quad
\vdash_{!^{m}\mathrm{ACT}_{\omega}^{\mathrm{foc}}+\mathcal H}
\cdot\Uparrow\Gamma\Rightarrow A\Uparrow\cdot
```

[L2062–L2064](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L2062-L2064)

```lean
theorem focusing {H : Theory} {Γ A} :
    Ordinary H Γ A ↔ Focused H (foc Γ A) :=
  ⟨focusing_complete, focused_sound⟩
```

Полное имя теоремы — `Focusing.focusing`. `focusing_complete` доказывает направление слева направо, `focused_sound` — обратное. Тип теоремы не содержит недоказанных математических предположений: `H`, `Γ`, `A` — произвольные параметры. В начале файла это же утверждение заранее выписано в комментарии [L164–L171](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L164-L171); комментарий поясняет цель, а приведённое выше объявление содержит её проверяемое Lean доказательство.

## 6. Как проверить доказательство

### На GitHub, без установки Lean

1. Откройте вкладку [**Actions**](https://github.com/tpshenitsyn/actmult-focusing/actions) и выберите **Verify Lean proof**.
2. Откройте успешный запуск для интересующей вас версии репозитория. Сверьте ветку и идентификатор коммита: зелёная галочка старого запуска относится к старой версии файлов.
3. Откройте задание **verify** и шаг сборки Lean/Lake. Он выполняет `lake build`: Lean проверяет файл `FocusingComplete.lean` и доказательства в нём. Шаг должен завершиться успешно.
4. Откройте шаг **Check theorem specification and axiom dependencies**. Он запускает `lake env lean -DwarningAsError=true Audit.lean`. Успешное завершение означает, что совпала проверяемая формулировка теоремы и прошла проверка её зависимостей от аксиом.

Команды автоматической проверки можно прочитать в [`.github/workflows/main.yml`](.github/workflows/main.yml). Таким образом, значима не галочка сама по себе, а успешное выполнение **сборки и аудита** для выбранного коммита. GitHub позволяет просматривать эти журналы без знания Lean ([инструкция GitHub](https://docs.github.com/en/actions/how-tos/monitor-workflows/view-workflow-run-history)).

### Что проверяет аудит и какие есть зависимости

[`Audit.lean`](Audit.lean) применяет `Focusing.focusing` к явно записанной формулировке теоремы, а затем проверяет вывод `#print axioms` для `Focusing.focusing_complete` и `Focusing.focusing`. Ожидаемый список в обоих случаях — `[propext, Quot.sound]`: стандартные принципы Lean об экстенсиональности высказываний и фактортипах. В списке нет `sorryAx`, которым Lean помечает пропущенные доказательства. Поэтому появление такой зависимости приведёт к ошибке аудита. Это проверка всего доказательства теоремы, включая использованные ею леммы.

В аудите используется имя `root` из первой версии формализации; это определительное сокращение для того же `foc`, а не другая разметка:

[L177](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L177)

```lean
abbrev root (Γ : Context) (A : Formula) : Judgment := foc Γ A
```

Чтобы проверить отсутствие сторонних математических зависимостей, достаточно посмотреть три файла: в [первой строке `FocusingComplete.lean`](https://github.com/tpshenitsyn/actmult-focusing/blob/567150af3c59a71fd6be9c490e550207611157b7/FocusingComplete.lean#L1) импортируется только `Std`; в [`lakefile.toml`](lakefile.toml) нет подключаемых пакетов, а в [`lake-manifest.json`](lake-manifest.json) список `packages` пуст. Все специальные определения и доказательства находятся в самом `FocusingComplete.lean`. Доказательство опирается на ядро Lean и перечисленные стандартные принципы. Версия Lean зафиксирована в [`lean-toolchain`](lean-toolchain).

### На своём компьютере

Установите Lean по [официальной инструкции](https://lean-lang.org/install/), скачайте репозиторий через **Code → Download ZIP** и распакуйте архив. Откройте терминал в распакованной папке и выполните:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
```

При первом запуске менеджер Lean может скачать версию **4.19.0**, указанную в `lean-toolchain`. Обе команды должны завершиться без ошибок; отсутствие вывода у второй команды нормально: ожидаемые сообщения уже проверены внутри `Audit.lean`.

