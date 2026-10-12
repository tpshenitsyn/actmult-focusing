import Std

/-! Complete focusing for ACTMult, Lean 4.19.0.
Self-contained: no local modules or Mathlib required.

Part I contains exactly the definitions needed to state the main theorem.
Part II introduces auxiliary definitions and proves the theorem.
-/

namespace Focusing

/-! ## Part I. Definitions of the theorem's calculi and initial marking -/

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

abbrev Context := List Formula
abbrev Theory := Formula → Prop

namespace Formula

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

end Formula

/-- `active` means C ↑ ·; `stored` means · ↑ C. -/
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

def foc (Γ : Context) (A : Formula) : Judgment :=
  .up [] Γ A .active

open Formula Judgment Side

/-- The original calculus with arbitrary cuts and hypotheses. -/
inductive Ordinary (H : Theory) : Context → Formula → Prop where
  | identity (p) : Ordinary H [atom p] (atom p)
  | tensorL {L R A B C} : Ordinary H (L ++ A :: B :: R) C →
      Ordinary H (L ++ tensor A B :: R) C
  | tensorR {Γ Δ A B} : Ordinary H Γ A → Ordinary H Δ B →
      Ordinary H (Γ ++ Δ) (tensor A B)
  | ldivL {L Ξ R A B C} : Ordinary H (L ++ B :: R) C →
      Ordinary H Ξ A → Ordinary H (L ++ Ξ ++ ldiv A B :: R) C
  | ldivR {Γ A B} : Ordinary H (A :: Γ) B → Ordinary H Γ (ldiv A B)
  | rdivL {L Ξ R A B C} : Ordinary H (L ++ B :: R) C →
      Ordinary H Ξ A → Ordinary H (L ++ rdiv B A :: (Ξ ++ R)) C
  | rdivR {Γ A B} : Ordinary H (Γ ++ [A]) B → Ordinary H Γ (rdiv B A)
  | zeroL (L R C) : Ordinary H (L ++ zero :: R) C
  | oneL {L R C} : Ordinary H (L ++ R) C → Ordinary H (L ++ one :: R) C
  | oneR : Ordinary H [] one
  | conjL₁ {L R A B C} : Ordinary H (L ++ A :: R) C →
      Ordinary H (L ++ conj A B :: R) C
  | conjL₂ {L R A B C} : Ordinary H (L ++ B :: R) C →
      Ordinary H (L ++ conj A B :: R) C
  | conjR {Γ A B} : Ordinary H Γ A → Ordinary H Γ B →
      Ordinary H Γ (conj A B)
  | disjL {L R A B C} : Ordinary H (L ++ A :: R) C →
      Ordinary H (L ++ B :: R) C → Ordinary H (L ++ disj A B :: R) C
  | disjR₁ {Γ A B} : Ordinary H Γ A → Ordinary H Γ (disj A B)
  | disjR₂ {Γ A B} : Ordinary H Γ B → Ordinary H Γ (disj A B)
  | starL {L R A C} :
      (∀ n : Nat, Ordinary H (L ++ List.replicate n A ++ R) C) →
      Ordinary H (L ++ star A :: R) C
  | starR {A} (parts : List Context) :
      (∀ Γ ∈ parts, Ordinary H Γ A) → Ordinary H parts.flatten (star A)
  | bangL {L R A C} (n : Nat) :
      Ordinary H (L ++ List.replicate n A ++ R) C →
      Ordinary H (L ++ bang A :: R) C
  | bangR {A B} : Ordinary H [A] B → Ordinary H [bang A] (bang B)
  | hypothesis {A} : H A → Ordinary H [] A
  | cut {L R Ξ A C} : Ordinary H Ξ A → Ordinary H (L ++ A :: R) C →
      Ordinary H (L ++ Ξ ++ R) C

/-- The focused rules of the dissertation, plus decide_H.
No positivity restriction is imposed on passive contexts. -/
inductive Focused (H : Theory) : Judgment → Prop where
  | identity (p) : Focused H (.right [atom p] (atom p))
  | tensorL {L R A B C s} : Focused H (.up L (A :: B :: R) C s) →
      Focused H (.up L (tensor A B :: R) C s)
  | ldivR {Γ A B} : Focused H (.up [] (A :: Γ) B .active) →
      Focused H (.up Γ [] (ldiv A B) .active)
  | rdivR {Γ A B} : Focused H (.up Γ [A] B .active) →
      Focused H (.up Γ [] (rdiv B A) .active)
  | zeroL (L R C s) : Focused H (.up L (zero :: R) C s)
  | oneL {L R C s} : Focused H (.up L R C s) →
      Focused H (.up L (one :: R) C s)
  | disjL {L R A B C s} : Focused H (.up L (A :: R) C s) →
      Focused H (.up L (B :: R) C s) →
      Focused H (.up L (disj A B :: R) C s)
  | conjR {Γ A B} : Focused H (.up Γ [] A .active) →
      Focused H (.up Γ [] B .active) → Focused H (.up Γ [] (conj A B) .active)
  | starL {L R A C s} :
      (∀ n : Nat, Focused H (.up L (List.replicate n A ++ R) C s)) →
      Focused H (.up L (star A :: R) C s)
  | tensorR {Γ Δ A B} : Focused H (.right Γ A) → Focused H (.right Δ B) →
      Focused H (.right (Γ ++ Δ) (tensor A B))
  | ldivL {L Ξ R A B C} : Focused H (.left L B R C) →
      Focused H (.right Ξ A) → Focused H (.left (L ++ Ξ) (ldiv A B) R C)
  | rdivL {L Ξ R A B C} : Focused H (.left L B R C) →
      Focused H (.right Ξ A) → Focused H (.left L (rdiv B A) (Ξ ++ R) C)
  | oneR : Focused H (.right [] one)
  | conjL₁ {L R A B C} : Focused H (.left L A R C) →
      Focused H (.left L (conj A B) R C)
  | conjL₂ {L R A B C} : Focused H (.left L B R C) →
      Focused H (.left L (conj A B) R C)
  | disjR₁ {Γ A B} : Focused H (.right Γ A) → Focused H (.right Γ (disj A B))
  | disjR₂ {Γ A B} : Focused H (.right Γ B) → Focused H (.right Γ (disj A B))
  | starR {A} (parts : List Context) :
      (∀ Γ ∈ parts, Focused H (.right Γ A)) → Focused H (.right parts.flatten (star A))
  | bangL {L R A C} (n : Nat) :
      Focused H (.up L (List.replicate n A ++ R) C .stored) →
      Focused H (.up (L ++ bang A :: R) [] C .stored)
  | bangR {A B} : Focused H (.up [] [A] B .active) →
      Focused H (.up [bang A] [] (bang B) .stored)
  | releaseL {L R A C} : A.negative = false →
      Focused H (.up L (A :: R) C .stored) → Focused H (.left L A R C)
  | releaseR {Γ A} : A.rightRelease = true →
      Focused H (.up Γ [] A .active) → Focused H (.right Γ A)
  | storeL {L R A C s} : A.positive = false →
      Focused H (.up (L ++ [A]) R C s) → Focused H (.up L (A :: R) C s)
  | storeR {Γ A} : A.negative = false →
      Focused H (.up Γ [] A .stored) → Focused H (.up Γ [] A .active)
  | decideL {L R A C} : A.negative = true →
      Focused H (.left L A R C) → Focused H (.up (L ++ A :: R) [] C .stored)
  | decideR {Γ A} : A.rightSync = true →
      Focused H (.right Γ A) → Focused H (.up Γ [] A .stored)
  | decideH {L R A C} : H A →
      Focused H (.left L A R C) → Focused H (.up (L ++ R) [] C .stored)


/-!
The main statement, proved as `Focusing.focusing` below, is:

  ∀ {H : Theory} {Γ : Context} {A : Formula},
    Ordinary H Γ A ↔ Focused H (foc Γ A)

Here `foc Γ A` is exactly · ↑ Γ ⇒ A ↑ ·.
-/

/-! ## Part II. Auxiliary definitions and proofs -/

/-- Compatibility alias for the first published version's Audit.lean.
New theorem statements and proofs use `foc`. -/
abbrev root (Γ : Context) (A : Formula) : Judgment := foc Γ A

namespace Formula

def multiplex : Formula → Bool
  | .bang _ => true
  | _ => false

end Formula

namespace Judgment

def context : Judgment → Context
  | .up L R _ _ => L ++ R
  | .left L A R _ => L ++ A :: R
  | .right Γ _ => Γ

def succedent : Judgment → Formula
  | .up _ _ C _ | .left _ _ _ C | .right _ C => C

end Judgment

/-- Split immediately before the first positive formula. -/
def split : Context → Context × Context
  | [] => ([], [])
  | A :: Γ => if A.positive then ([], A :: Γ)
              else let p := split Γ; (A :: p.1, p.2)

def canonical (Γ : Context) (A : Formula) : Judgment :=
  let p := split Γ
  .up p.1 p.2 A (if A.negative then .active else .stored)

theorem split_append (Γ : Context) : (split Γ).1 ++ (split Γ).2 = Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    simp only [split]
    split <;> simp_all

@[simp] theorem canonical_context (Γ : Context) (A : Formula) :
    (canonical Γ A).context = Γ := by
  simp only [canonical, Judgment.context, split_append]

@[simp] theorem canonical_succedent (Γ : Context) (A : Formula) :
    (canonical Γ A).succedent = A := rfl

/-- ACTMult plus normalized cuts for the hypotheses H.
The star-left constructor has genuinely countably many premises. -/
inductive Unfocused (H : Theory) : Context → Formula → Prop where
  | identity (p) : Unfocused H [atom p] (atom p)
  | tensorL {L R A B C} : Unfocused H (L ++ A :: B :: R) C →
      Unfocused H (L ++ tensor A B :: R) C
  | tensorR {Γ Δ A B} : Unfocused H Γ A → Unfocused H Δ B →
      Unfocused H (Γ ++ Δ) (tensor A B)
  | ldivL {L Ξ R A B C} : Unfocused H (L ++ B :: R) C →
      Unfocused H Ξ A → Unfocused H (L ++ Ξ ++ ldiv A B :: R) C
  | ldivR {Γ A B} : Unfocused H (A :: Γ) B → Unfocused H Γ (ldiv A B)
  | rdivL {L Ξ R A B C} : Unfocused H (L ++ B :: R) C →
      Unfocused H Ξ A → Unfocused H (L ++ rdiv B A :: (Ξ ++ R)) C
  | rdivR {Γ A B} : Unfocused H (Γ ++ [A]) B → Unfocused H Γ (rdiv B A)
  | zeroL (L R C) : Unfocused H (L ++ zero :: R) C
  | oneL {L R C} : Unfocused H (L ++ R) C → Unfocused H (L ++ one :: R) C
  | oneR : Unfocused H [] one
  | conjL₁ {L R A B C} : Unfocused H (L ++ A :: R) C →
      Unfocused H (L ++ conj A B :: R) C
  | conjL₂ {L R A B C} : Unfocused H (L ++ B :: R) C →
      Unfocused H (L ++ conj A B :: R) C
  | conjR {Γ A B} : Unfocused H Γ A → Unfocused H Γ B →
      Unfocused H Γ (conj A B)
  | disjL {L R A B C} : Unfocused H (L ++ A :: R) C →
      Unfocused H (L ++ B :: R) C → Unfocused H (L ++ disj A B :: R) C
  | disjR₁ {Γ A B} : Unfocused H Γ A → Unfocused H Γ (disj A B)
  | disjR₂ {Γ A B} : Unfocused H Γ B → Unfocused H Γ (disj A B)
  | starL {L R A C} :
      (∀ n : Nat, Unfocused H (L ++ List.replicate n A ++ R) C) →
      Unfocused H (L ++ star A :: R) C
  | starR {A} (parts : List Context) :
      (∀ Γ ∈ parts, Unfocused H Γ A) → Unfocused H parts.flatten (star A)
  | bangL {L R A C} (n : Nat) :
      Unfocused H (L ++ List.replicate n A ++ R) C →
      Unfocused H (L ++ bang A :: R) C
  | bangR {A B} : Unfocused H [A] B → Unfocused H [bang A] (bang B)
  | ncut {L R A C} : H A → Unfocused H (L ++ A :: R) C →
      Unfocused H (L ++ R) C

end Focusing


/- ===== Focusing/Transport.lean ===== -/

namespace Focusing
open Formula Judgment Side

private theorem stable_relabel {H : Theory} {Γ A}
    (h : A.negative = false) (d : Focused H (.up Γ [] A .stored)) (t : Side) :
    Focused H (.up Γ [] A t) := by
  cases t with
  | active => exact .storeR h d
  | stored => exact d

/-- The store-right invertibility lemma, for an arbitrary active left suffix. -/
theorem up_relabel {H : Theory} {j : Judgment} (d : Focused H j) :
    ∀ {L R A s}, j = .up L R A s → A.negative = false →
      ∀ t, Focused H (.up L R A t) := by
  induction d <;> intro L R A s heq hn t <;> cases heq
  case tensorL d ih => exact .tensorL (ih rfl hn t)
  case ldivR => contradiction
  case rdivR => contradiction
  case zeroL => exact .zeroL _ _ _ _
  case oneL d ih => exact .oneL (ih rfl hn t)
  case disjL d₁ d₂ ih₁ ih₂ => exact .disjL (ih₁ rfl hn t) (ih₂ rfl hn t)
  case conjR => contradiction
  case starL d ih => exact .starL (fun n => ih n rfl hn t)
  case bangL n d ih => exact stable_relabel hn (.bangL n d) t
  case bangR d ih => exact stable_relabel hn (.bangR d) t
  case storeL hp d ih => exact .storeL hp (ih rfl hn t)
  case storeR hp d ih => exact ih rfl hn t
  case decideL hp d ih => exact stable_relabel hn (.decideL hp d) t
  case decideR hp d ih => exact stable_relabel hn (.decideR hp d) t
  case decideH hp d ih => exact stable_relabel hn (.decideH hp d) t

theorem store_right_iff {H : Theory} {L R A}
    (h : A.negative = false) :
    Focused H (.up L R A .active) ↔ Focused H (.up L R A .stored) :=
  ⟨fun d => up_relabel d rfl h .stored,
   fun d => up_relabel d rfl h .active⟩

/-- Inverting a store-left step does not require completeness. -/
theorem store_left_inverse {H : Theory} {L R A C s}
    (hp : A.positive = false) (d : Focused H (.up L (A :: R) C s)) :
    Focused H (.up (L ++ [A]) R C s) := by
  cases d with
  | tensorL => contradiction
  | zeroL => contradiction
  | oneL => contradiction
  | disjL => contradiction
  | starL => contradiction
  | storeL _ d => exact d

/-- Moving the cursor across the maximal nonpositive prefix. -/
theorem up_scan_iff {H : Theory} (L Γ : Context) (C : Formula) (s : Side) :
    Focused H (.up L Γ C s) ↔
    Focused H (.up (L ++ (split Γ).1) (split Γ).2 C s) := by
  induction Γ generalizing L with
  | nil => simp [split]
  | cons A Γ ih =>
    cases hp : A.positive with
    | true => simp [split, hp]
    | false =>
      have hs : Focused H (.up L (A :: Γ) C s) ↔
          Focused H (.up (L ++ [A]) Γ C s) :=
        ⟨store_left_inverse hp, Focused.storeL hp⟩
      simpa [split, hp, List.append_assoc] using hs.trans (ih (L ++ [A]))

/-- Equivalence of the theorem's foc judgment and the canonical judgment. -/
theorem foc_iff_canonical {H : Theory} {Γ : Context} {A : Formula} :
    Focused H (foc Γ A) ↔ Focused H (canonical Γ A) := by
  have hs := up_scan_iff (H := H) [] Γ A .active
  simp only [List.nil_append] at hs
  cases hn : A.negative with
  | true => simpa [foc, canonical, hn] using hs
  | false =>
    simpa [foc, canonical, hn] using hs.trans (store_right_iff hn)

end Focusing


/- ===== Focusing/Asynchronous.lean ===== -/

namespace Focusing
open Formula Judgment Side

/-- These invertibility results concern the formula immediately after ↑.
They do not assert the harder arbitrary-position canonical invertibility. -/
theorem tensor_left_iff {H : Theory} {L R A B C s} :
    Focused H (.up L (tensor A B :: R) C s) ↔
    Focused H (.up L (A :: B :: R) C s) := by
  constructor
  · intro d
    cases d with
    | tensorL d => exact d
    | storeL h _ => contradiction
  · exact Focused.tensorL

theorem one_left_iff {H : Theory} {L R C s} :
    Focused H (.up L (one :: R) C s) ↔ Focused H (.up L R C s) := by
  constructor
  · intro d
    cases d with
    | oneL d => exact d
    | storeL h _ => contradiction
  · exact Focused.oneL

theorem disj_left_iff {H : Theory} {L R A B C s} :
    Focused H (.up L (disj A B :: R) C s) ↔
    Focused H (.up L (A :: R) C s) ∧ Focused H (.up L (B :: R) C s) := by
  constructor
  · intro d
    cases d with
    | disjL d₁ d₂ => exact ⟨d₁, d₂⟩
    | storeL h _ => contradiction
  · rintro ⟨d₁, d₂⟩
    exact .disjL d₁ d₂

theorem star_left_iff {H : Theory} {L R A C s} :
    Focused H (.up L (star A :: R) C s) ↔
    ∀ n : Nat, Focused H (.up L (List.replicate n A ++ R) C s) := by
  constructor
  · intro d
    cases d with
    | starL ds => exact ds
    | storeL h _ => contradiction
  · exact Focused.starL

theorem ldiv_right_iff {H : Theory} {Γ A B} :
    Focused H (.up Γ [] (ldiv A B) .active) ↔
    Focused H (.up [] (A :: Γ) B .active) := by
  constructor
  · intro d
    cases d with
    | ldivR d => exact d
    | storeR h _ => contradiction
  · exact Focused.ldivR

theorem rdiv_right_iff {H : Theory} {Γ A B} :
    Focused H (.up Γ [] (rdiv B A) .active) ↔
    Focused H (.up Γ [A] B .active) := by
  constructor
  · intro d
    cases d with
    | rdivR d => exact d
    | storeR h _ => contradiction
  · exact Focused.rdivR

theorem conj_right_iff {H : Theory} {Γ A B} :
    Focused H (.up Γ [] (conj A B) .active) ↔
    Focused H (.up Γ [] A .active) ∧ Focused H (.up Γ [] B .active) := by
  constructor
  · intro d
    cases d with
    | conjR d₁ d₂ => exact ⟨d₁, d₂⟩
    | storeR h _ => contradiction
  · rintro ⟨d₁, d₂⟩
    exact .conjR d₁ d₂

end Focusing


/- ===== Focusing/Expansion.lean ===== -/

/-! Asynchronous left expansion, including all finite powers of star. -/
namespace Focusing
open Formula Judgment Side

inductive Expands : Formula → Context → Prop where
  | keep {A} : A.positive = false → Expands A [A]
  | one : Expands .one []
  | tensor {A B Γ Δ} : Expands A Γ → Expands B Δ → Expands (.tensor A B) (Γ ++ Δ)
  | disj₁ {A B Γ} : Expands A Γ → Expands (.disj A B) Γ
  | disj₂ {A B Γ} : Expands B Γ → Expands (.disj A B) Γ
  | star {A} (parts : List Context) :
      (∀ Γ ∈ parts, Expands A Γ) → Expands (.star A) parts.flatten

inductive ExpandsContext : Context → Context → Prop where
  | nil : ExpandsContext [] []
  | cons {A Γ Δ Ξ} : Expands A Δ → ExpandsContext Γ Ξ →
      ExpandsContext (A :: Γ) (Δ ++ Ξ)

namespace ExpandsContext

theorem append {Γ Δ Γ' Δ'} (h : ExpandsContext Γ Γ') (k : ExpandsContext Δ Δ') :
    ExpandsContext (Γ ++ Δ) (Γ' ++ Δ') := by
  induction h with
  | nil => simpa using k
  | cons e h ih => simpa [List.append_assoc] using ExpandsContext.cons e ih

theorem split_append {Γ Δ Ξ} (h : ExpandsContext (Γ ++ Δ) Ξ) :
    ∃ Γ' Δ', Ξ = Γ' ++ Δ' ∧ ExpandsContext Γ Γ' ∧ ExpandsContext Δ Δ' := by
  induction Γ generalizing Ξ with
  | nil => exact ⟨[], Ξ, rfl, .nil, h⟩
  | cons A Γ ih =>
    cases h with
    | cons e h =>
      obtain ⟨Γ', Δ', rfl, eΓ, eΔ⟩ := ih h
      exact ⟨_, _, (List.append_assoc ..).symm, .cons e eΓ, eΔ⟩

theorem replicate {A n Γ} (h : ExpandsContext (List.replicate n A) Γ) :
    ∃ parts : List Context, parts.length = n ∧ parts.flatten = Γ ∧
      ∀ Δ ∈ parts, Expands A Δ := by
  induction n generalizing Γ with
  | zero => cases h; exact ⟨[], rfl, rfl, by simp⟩
  | succ n ih =>
    cases h with
    | cons e h =>
      obtain ⟨parts, hn, rfl, hp⟩ := ih h
      refine ⟨_ :: parts, by simp [hn], rfl, ?_⟩
      intro Δ hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact e
      · exact hp Δ hm

end ExpandsContext

theorem expand_build {H : Theory} (A : Formula) :
    ∀ {L R C s},
    (∀ Δ, Expands A Δ → Focused H (.up (L ++ Δ) R C s)) →
    Focused H (.up L (A :: R) C s) := by
  induction A with
  | atom p => intro L R C s h; exact .storeL rfl (h _ (.keep rfl))
  | zero => intro L R C s h; exact .zeroL _ _ _ _
  | one => intro L R C s h; exact .oneL (by simpa using h _ .one)
  | tensor A B ihA ihB =>
    intro L R C s h
    apply Focused.tensorL
    apply ihA
    intro Δ eΔ
    apply ihB
    intro Ξ eΞ
    simpa [List.append_assoc] using h _ (.tensor eΔ eΞ)
  | ldiv A B => intro L R C s h; exact .storeL rfl (h _ (.keep rfl))
  | rdiv A B => intro L R C s h; exact .storeL rfl (h _ (.keep rfl))
  | conj A B => intro L R C s h; exact .storeL rfl (h _ (.keep rfl))
  | disj A B ihA ihB =>
    intro L R C s h
    exact .disjL (ihA (fun Δ e => h Δ (.disj₁ e)))
      (ihB (fun Δ e => h Δ (.disj₂ e)))
  | bang A => intro L R C s h; exact .storeL rfl (h _ (.keep rfl))
  | star A ih =>
    intro L R C s h
    apply Focused.starL
    intro n
    have build : ∀ n L, (∀ parts : List Context, parts.length = n →
        (∀ Δ ∈ parts, Expands A Δ) →
        Focused H (.up (L ++ parts.flatten) R C s)) →
        Focused H (.up L (List.replicate n A ++ R) C s) := by
      intro n
      induction n with
      | zero => intro L k; simpa using k [] rfl (by simp)
      | succ n ihn =>
        intro L k
        apply ih
        intro Δ eΔ
        apply ihn
        intro parts hn hp
        have hh := k (Δ :: parts) (by simp [hn]) (by
          intro Ξ hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact eΔ
          · exact hp Ξ hm)
        simpa [List.flatten_cons, List.append_assoc] using hh
    exact build n L (fun parts _ hp => h _ (.star parts hp))

theorem expand_context_build {H : Theory} (Γ : Context) :
    ∀ {L R C s}, (∀ Δ, ExpandsContext Γ Δ →
      Focused H (.up (L ++ Δ) R C s)) →
      Focused H (.up L (Γ ++ R) C s) := by
  induction Γ with
  | nil => intro L R C s h; simpa using h [] .nil
  | cons A Γ ih =>
    intro L R C s h
    apply expand_build A
    intro Δ eΔ
    apply ih
    intro Ξ eΞ
    simpa [List.append_assoc] using h _ (.cons eΔ eΞ)

theorem expand_take {H : Theory} {A Δ} (e : Expands A Δ) :
    ∀ {L R C s}, Focused H (.up L (A :: R) C s) →
      Focused H (.up (L ++ Δ) R C s) := by
  induction e with
  | keep hp => intro L R C s d; exact store_left_inverse hp d
  | one => intro L R C s d; simpa using one_left_iff.mp d
  | tensor e₁ e₂ ih₁ ih₂ =>
    intro L R C s d
    simpa [List.append_assoc] using ih₂ (ih₁ (tensor_left_iff.mp d))
  | disj₁ e ih => intro L R C s d; exact ih (disj_left_iff.mp d).1
  | disj₂ e ih => intro L R C s d; exact ih (disj_left_iff.mp d).2
  | @star A parts hp ih =>
    intro L R C s d
    have take : ∀ parts : List Context,
        (∀ Δ ∈ parts, ∀ {L R C s}, Focused H (.up L (A :: R) C s) →
          Focused H (.up (L ++ Δ) R C s)) →
        ∀ {L R C s}, Focused H (.up L (List.replicate parts.length A ++ R) C s) →
          Focused H (.up (L ++ parts.flatten) R C s) := by
      intro parts
      induction parts with
      | nil => intro _ L R C s d; simpa using d
      | cons Δ parts ihn =>
        intro hk L R C s d
        have d₁ := hk Δ (by simp) d
        have d₂ := ihn (fun Ξ hm => hk Ξ (by simp [hm])) d₁
        simpa [List.flatten_cons, List.append_assoc] using d₂
    exact take parts ih (star_left_iff.mp d parts.length)

theorem expand_context_take {H : Theory} {Γ Δ} (e : ExpandsContext Γ Δ) :
    ∀ {L R C s}, Focused H (.up L (Γ ++ R) C s) →
      Focused H (.up (L ++ Δ) R C s) := by
  induction e with
  | nil => intro L R C s d; simpa using d
  | cons e h ih =>
    intro L R C s d
    simpa [List.append_assoc] using ih (expand_take e d)

theorem scan_expansion_iff {H : Theory} {L Γ R C s} :
    Focused H (.up L (Γ ++ R) C s) ↔
    ∀ Δ, ExpandsContext Γ Δ → Focused H (.up (L ++ Δ) R C s) :=
  ⟨fun d _ e => expand_context_take e d, expand_context_build Γ⟩

end Focusing


/- ===== Focusing/Permutation.lean ===== -/

/-! Asynchronous permutations in arbitrary context positions. -/
namespace Focusing
open Formula Judgment Side

abbrev Nonpositive (Γ : Context) : Prop := ∀ A ∈ Γ, A.positive = false

theorem Expands.nonpositive {A Γ} (e : Expands A Γ) : Nonpositive Γ := by
  induction e with
  | keep h => simpa [Nonpositive] using h
  | one => simp [Nonpositive]
  | tensor e₁ e₂ ih₁ ih₂ =>
    intro A h
    rcases List.mem_append.mp h with h | h
    · exact ih₁ A h
    · exact ih₂ A h
  | disj₁ e ih => exact ih
  | disj₂ e ih => exact ih
  | star parts h ih =>
    intro A hA
    obtain ⟨Γ, hΓ, hA⟩ := List.mem_flatten.mp hA
    exact ih Γ hΓ A hA

theorem ExpandsContext.nonpositive {Γ Δ} (e : ExpandsContext Γ Δ) : Nonpositive Δ := by
  induction e with
  | nil => simp [Nonpositive]
  | cons e h ih =>
    intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact e.nonpositive A hA
    · exact ih A hA

theorem scan_nonpositive_iff {H : Theory} {Γ} (h : Nonpositive Γ) {L R C s} :
    Focused H (.up L (Γ ++ R) C s) ↔ Focused H (.up (L ++ Γ) R C s) := by
  induction Γ generalizing L with
  | nil => simp
  | cons A Γ ih =>
    have hp := h A (by simp)
    have ht : Nonpositive Γ := fun B hb => h B (by simp [hb])
    have hs : Focused H (.up L (A :: (Γ ++ R)) C s) ↔
        Focused H (.up (L ++ [A]) (Γ ++ R) C s) :=
      ⟨store_left_inverse hp, Focused.storeL hp⟩
    simpa [List.append_assoc] using hs.trans (ih ht)

theorem expand_block_iff {H : Theory} (P Γ R L : Context) (C : Formula) (s : Side) :
    Focused H (.up L (P ++ Γ ++ R) C s) ↔
    ∀ Δ, ExpandsContext Γ Δ → Focused H (.up L (P ++ Δ ++ R) C s) := by
  simp only [List.append_assoc]
  constructor
  · intro d Δ eΔ
    apply expand_context_build P
    intro Ξ eΞ
    have d₁ := expand_context_take eΞ (R := Γ ++ R) (by simpa [List.append_assoc] using d)
    have d₂ := expand_context_take eΔ d₁
    exact (scan_nonpositive_iff eΔ.nonpositive).mpr d₂
  · intro h
    apply expand_context_build P
    intro Ξ eΞ
    apply expand_context_build Γ
    intro Δ eΔ
    have d₁ := expand_context_take eΞ (R := Δ ++ R) (by simpa [List.append_assoc] using h Δ eΔ)
    exact (scan_nonpositive_iff eΔ.nonpositive).mp d₁

theorem tensor_left_any_iff {H : Theory} {L R A B C} :
    Focused H (foc (L ++ tensor A B :: R) C) ↔
    Focused H (foc (L ++ A :: B :: R) C) := by
  unfold foc
  constructor
  · intro d
    apply expand_context_build L
    intro Δ eΔ
    exact tensor_left_iff.mp (expand_context_take eΔ d)
  · intro d
    apply expand_context_build L
    intro Δ eΔ
    exact .tensorL (expand_context_take eΔ d)

theorem one_left_any_iff {H : Theory} {L R C} :
    Focused H (foc (L ++ one :: R) C) ↔ Focused H (foc (L ++ R) C) := by
  unfold foc
  constructor
  · intro d
    apply expand_context_build L
    intro Δ eΔ
    exact one_left_iff.mp (expand_context_take eΔ d)
  · intro d
    apply expand_context_build L
    intro Δ eΔ
    exact .oneL (expand_context_take eΔ d)

theorem disj_left_any_iff {H : Theory} {L R A B C} :
    Focused H (foc (L ++ disj A B :: R) C) ↔
    Focused H (foc (L ++ A :: R) C) ∧ Focused H (foc (L ++ B :: R) C) := by
  unfold foc
  constructor
  · intro d
    constructor
    · apply expand_context_build L
      intro Δ eΔ
      exact (disj_left_iff.mp (expand_context_take eΔ d)).1
    · apply expand_context_build L
      intro Δ eΔ
      exact (disj_left_iff.mp (expand_context_take eΔ d)).2
  · rintro ⟨d₁, d₂⟩
    apply expand_context_build L
    intro Δ eΔ
    exact .disjL (expand_context_take eΔ d₁) (expand_context_take eΔ d₂)

theorem star_left_any_iff {H : Theory} {L R A C} :
    Focused H (foc (L ++ star A :: R) C) ↔
    ∀ n, Focused H (foc (L ++ List.replicate n A ++ R) C) := by
  unfold foc
  constructor
  · intro d n
    rw [List.append_assoc]
    apply expand_context_build L
    intro Δ eΔ
    exact star_left_iff.mp (expand_context_take eΔ d) n
  · intro h
    apply expand_context_build L
    intro Δ eΔ
    exact .starL (fun n => expand_context_take eΔ (by simpa [List.append_assoc] using h n))

theorem zero_left_any {H : Theory} (L R : Context) (C : Formula) :
    Focused H (foc (L ++ zero :: R) C) := by
  apply expand_context_build L
  intro Δ eΔ
  exact .zeroL _ _ _ _

theorem scan_empty_build {H : Theory} (Γ : Context) {L C s}
    (h : ∀ Δ, ExpandsContext Γ Δ → Focused H (.up (L ++ Δ) [] C s)) :
    Focused H (.up L Γ C s) := by
  simpa using expand_context_build Γ (R := []) h

theorem ldiv_right_any_iff {H : Theory} {Γ A B} :
    Focused H (foc Γ (ldiv A B)) ↔ Focused H (foc (A :: Γ) B) := by
  have eqv := expand_block_iff (H := H) [A] Γ [] [] B .active
  simp only [List.append_nil, List.singleton_append] at eqv
  constructor
  · intro d
    apply eqv.mpr
    intro Δ eΔ
    exact ldiv_right_iff.mp (expand_context_take eΔ (R := []) (by simpa [foc] using d))
  · intro d
    apply scan_empty_build Γ
    intro Δ eΔ
    apply Focused.ldivR
    exact eqv.mp d Δ eΔ

theorem rdiv_right_any_iff {H : Theory} {Γ A B} :
    Focused H (foc Γ (rdiv B A)) ↔ Focused H (foc (Γ ++ [A]) B) := by
  unfold foc
  constructor
  · intro d
    apply expand_context_build Γ
    intro Δ eΔ
    exact rdiv_right_iff.mp (expand_context_take eΔ (R := []) (by simpa using d))
  · intro d
    apply scan_empty_build Γ
    intro Δ eΔ
    exact .rdivR (expand_context_take eΔ d)

theorem conj_right_any_iff {H : Theory} {Γ A B} :
    Focused H (foc Γ (conj A B)) ↔
    Focused H (foc Γ A) ∧ Focused H (foc Γ B) := by
  unfold foc
  constructor
  · intro d
    constructor
    · apply scan_empty_build Γ
      intro Δ eΔ
      exact (conj_right_iff.mp (expand_context_take eΔ (R := []) (by simpa using d))).1
    · apply scan_empty_build Γ
      intro Δ eΔ
      exact (conj_right_iff.mp (expand_context_take eΔ (R := []) (by simpa using d))).2
  · rintro ⟨d₁, d₂⟩
    apply scan_empty_build Γ
    intro Δ eΔ
    exact .conjR (expand_context_take eΔ (R := []) (by simpa using d₁))
      (expand_context_take eΔ (R := []) (by simpa using d₂))

theorem foc_expand_block {H : Theory} {P Γ R Δ C}
    (d : Focused H (foc (P ++ Γ ++ R) C)) (e : ExpandsContext Γ Δ) :
    Focused H (foc (P ++ Δ ++ R) C) :=
  (expand_block_iff P Γ R [] C .active).mp d Δ e

end Focusing


/- ===== Focusing/Replacement.lean ===== -/

namespace Focusing
open Formula Judgment Side

/-- Replace one designated occurrence by a context. -/
inductive Replace (T : Formula) (K : Context) : Context → Context → Prop where
  | here (R) : Replace T K (T :: R) (K ++ R)
  | there {Γ Δ} (A) : Replace T K Γ Δ → Replace T K (A :: Γ) (A :: Δ)

namespace Replace

theorem prepend {T K Γ Δ} (d : Replace T K Γ Δ) (L : Context) :
    Replace T K (L ++ Γ) (L ++ Δ) := by
  induction L with
  | nil => exact d
  | cons A L ih => exact .there A ih

theorem suffix {T K Γ Δ} (d : Replace T K Γ Δ) (R : Context) :
    Replace T K (Γ ++ R) (Δ ++ R) := by
  induction d with
  | here Γ => simpa [List.append_assoc] using (Replace.here (T := T) (K := K) (Γ ++ R))
  | there A d ih => exact .there A ih

theorem of_append {T K L R Δ} (d : Replace T K (L ++ R) Δ) :
    (∃ L', Replace T K L L' ∧ Δ = L' ++ R) ∨
    (∃ R', Replace T K R R' ∧ Δ = L ++ R') := by
  induction L generalizing Δ with
  | nil => exact .inr ⟨Δ, d, rfl⟩
  | cons A L ih =>
    cases d with
    | here => exact .inl ⟨K ++ L, .here _, (List.append_assoc ..).symm⟩
    | there A d =>
      rcases ih d with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
      · exact .inl ⟨A :: L', .there A h, rfl⟩
      · exact .inr ⟨R', h, rfl⟩

theorem flatten_lift {T K} (P : Context → Prop) (parts : List Context)
    (orig : ∀ Γ ∈ parts, P Γ)
    (step : ∀ Γ ∈ parts, ∀ Δ, Replace T K Γ Δ → P Δ)
    {Δ} (d : Replace T K parts.flatten Δ) :
    ∃ parts' : List Context, parts'.flatten = Δ ∧ ∀ Γ ∈ parts', P Γ := by
  induction parts generalizing Δ with
  | nil => cases d
  | cons Γ parts ih =>
    rcases of_append d with ⟨Γ', h, rfl⟩ | ⟨Δ', h, rfl⟩
    · refine ⟨Γ' :: parts, rfl, ?_⟩
      intro Ξ hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact step Γ (by simp) Ξ h
      · exact orig Ξ (by simp [hm])
    · obtain ⟨parts', hp, hh⟩ := ih
        (fun Ξ hm => orig Ξ (by simp [hm]))
        (fun Ξ hm => step Ξ (by simp [hm])) h
      refine ⟨Γ :: parts', by simp [hp], ?_⟩
      intro Ξ hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact orig Ξ (by simp)
      · exact hh Ξ hm

end Replace

inductive ReplaceJudgment (T : Formula) (K : Context) : Judgment → Judgment → Prop where
  | upL {L L' R C s} : Replace T K L L' →
      ReplaceJudgment T K (.up L R C s) (.up L' R C s)
  | upR {L R R' C s} : Replace T K R R' →
      ReplaceJudgment T K (.up L R C s) (.up L R' C s)
  | leftL {L L' A R C} : Replace T K L L' →
      ReplaceJudgment T K (.left L A R C) (.left L' A R C)
  | leftR {L A R R' C} : Replace T K R R' →
      ReplaceJudgment T K (.left L A R C) (.left L A R' C)
  | right {Γ Γ' A} : Replace T K Γ Γ' →
      ReplaceJudgment T K (.right Γ A) (.right Γ' A)

/-- Replace a negative formula in every passive zone, given its focused case.
This single structural induction handles all phase changes and omega rules. -/
theorem replace_negative {H : Theory} {T : Formula} {K : Context}
    (hn : T.negative = true) (nk : Nonpositive K)
    (critical : ∀ {L R C}, Focused H (.left L T R C) →
      Focused H (.up (L ++ K ++ R) [] C .stored))
    {j} (d : Focused H j) :
    ∀ {j'}, ReplaceJudgment T K j j' → Focused H j' := by
  induction d with
  | identity p =>
    intro j' e
    cases e with
    | right e => cases e with
      | here => contradiction
      | there _ e => cases e
  | tensorL d ih =>
    intro j' e
    cases e with
    | upL e => exact .tensorL (ih (.upL e))
    | upR e => cases e with
      | here => contradiction
      | there _ e => exact .tensorL (ih (.upR (.there _ (.there _ e))))
  | ldivR d ih =>
    intro j' e
    cases e with
    | upL e => exact .ldivR (ih (.upR (.there _ e)))
    | upR e => cases e
  | rdivR d ih =>
    intro j' e
    cases e with
    | upL e => exact .rdivR (ih (.upL e))
    | upR e => cases e
  | zeroL =>
    intro j' e
    cases e with
    | upL => exact .zeroL _ _ _ _
    | upR e => cases e with
      | here => contradiction
      | there _ e => exact .zeroL _ _ _ _
  | oneL d ih =>
    intro j' e
    cases e with
    | upL e => exact .oneL (ih (.upL e))
    | upR e => cases e with
      | here => contradiction
      | there _ e => exact .oneL (ih (.upR e))
  | disjL d₁ d₂ ih₁ ih₂ =>
    intro j' e
    cases e with
    | upL e => exact .disjL (ih₁ (.upL e)) (ih₂ (.upL e))
    | upR e => cases e with
      | here => contradiction
      | there _ e => exact .disjL (ih₁ (.upR (.there _ e))) (ih₂ (.upR (.there _ e)))
  | conjR d₁ d₂ ih₁ ih₂ =>
    intro j' e
    cases e with
    | upL e => exact .conjR (ih₁ (.upL e)) (ih₂ (.upL e))
    | upR e => cases e
  | starL ds ih =>
    intro j' e
    cases e with
    | upL e => exact .starL (fun n => ih n (.upL e))
    | upR e => cases e with
      | here => contradiction
      | there _ e => exact .starL (fun n => ih n (.upR (e.prepend _)))
  | tensorR d₁ d₂ ih₁ ih₂ =>
    intro j' e
    cases e with
    | right e =>
      rcases e.of_append with ⟨Γ', h, rfl⟩ | ⟨Δ', h, rfl⟩
      · exact .tensorR (ih₁ (.right h)) d₂
      · exact .tensorR d₁ (ih₂ (.right h))
  | ldivL d₁ d₂ ih₁ ih₂ =>
    intro j' e
    cases e with
    | leftL e =>
      rcases e.of_append with ⟨L', h, rfl⟩ | ⟨Ξ', h, rfl⟩
      · exact .ldivL (ih₁ (.leftL h)) d₂
      · exact .ldivL d₁ (ih₂ (.right h))
    | leftR e => exact .ldivL (ih₁ (.leftR e)) d₂
  | rdivL d₁ d₂ ih₁ ih₂ =>
    intro j' e
    cases e with
    | leftL e => exact .rdivL (ih₁ (.leftL e)) d₂
    | leftR e =>
      rcases e.of_append with ⟨Ξ', h, rfl⟩ | ⟨R', h, rfl⟩
      · exact .rdivL d₁ (ih₂ (.right h))
      · exact .rdivL (ih₁ (.leftR h)) d₂
  | oneR => intro j' e; cases e with
    | right e => cases e
  | conjL₁ d ih =>
    intro j' e
    cases e with
    | leftL e => exact .conjL₁ (ih (.leftL e))
    | leftR e => exact .conjL₁ (ih (.leftR e))
  | conjL₂ d ih =>
    intro j' e
    cases e with
    | leftL e => exact .conjL₂ (ih (.leftL e))
    | leftR e => exact .conjL₂ (ih (.leftR e))
  | disjR₁ d ih => intro j' e; cases e with
    | right e => exact .disjR₁ (ih (.right e))
  | disjR₂ d ih => intro j' e; cases e with
    | right e => exact .disjR₂ (ih (.right e))
  | starR parts ds ih =>
    intro j' e
    cases e with
    | right e =>
      obtain ⟨parts', rfl, hp⟩ := e.flatten_lift (fun Γ => Focused H (.right Γ _)) parts ds
        (fun Γ hm Δ ed => ih Γ hm (.right ed))
      exact .starR parts' hp
  | bangL n d ih =>
    intro j' e
    cases e with
    | upL e =>
      rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
      · exact .bangL n (ih (.upL h))
      · cases h with
        | here => contradiction
        | there _ h => exact .bangL n (ih (.upR (h.prepend _)))
    | upR e => cases e
  | bangR d ih =>
    intro j' e
    cases e with
    | upL e => cases e with
      | here => contradiction
      | there _ e => cases e
    | upR e => cases e
  | releaseL hp d ih =>
    intro j' e
    cases e with
    | leftL e => exact .releaseL hp (ih (.upL e))
    | leftR e => exact .releaseL hp (ih (.upR (.there _ e)))
  | releaseR hp d ih => intro j' e; cases e with
    | right e => exact .releaseR hp (ih (.upL e))
  | storeL hp d ih =>
    intro j' e
    cases e with
    | upL e => exact .storeL hp (ih (.upL (e.suffix _)))
    | upR e => cases e with
      | here =>
        apply (scan_nonpositive_iff nk).mpr
        simpa using ih (.upL ((Replace.here []).prepend _))
      | there _ e => exact .storeL hp (ih (.upR e))
  | storeR hp d ih =>
    intro j' e
    cases e with
    | upL e => exact .storeR hp (ih (.upL e))
    | upR e => cases e
  | decideL hp d ih =>
    intro j' e
    cases e with
    | upL e =>
      rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
      · exact .decideL hp (ih (.leftL h))
      · cases h with
        | here => simpa [List.append_assoc] using critical d
        | there _ h => exact .decideL hp (ih (.leftR h))
    | upR e => cases e
  | decideR hp d ih =>
    intro j' e
    cases e with
    | upL e => exact .decideR hp (ih (.right e))
    | upR e => cases e
  | decideH hp d ih =>
    intro j' e
    cases e with
    | upL e =>
      rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
      · exact .decideH hp (ih (.leftL h))
      · exact .decideH hp (ih (.leftR h))
    | upR e => cases e

end Focusing


/- ===== Focusing/CutConsumer.lean ===== -/

namespace Focusing
open Formula

abbrev CutAt (H : Theory) (A : Formula) : Prop :=
  ∀ {Γ L R C}, Unfocused H Γ A → Unfocused H (L ++ A :: R) C →
    Unfocused H (L ++ Γ ++ R) C

/-- Principal reductions required after the producer ends in a right rule. -/
def PrincipalCut (H : Theory) (T : Formula) (Γ : Context) : Prop :=
  match T with
  | .atom _ => True
  | .zero => ∀ L R C, Unfocused H (L ++ Γ ++ R) C
  | .one => ∀ {L R C}, Unfocused H (L ++ R) C → Unfocused H (L ++ Γ ++ R) C
  | .tensor A B => ∀ {L R C}, Unfocused H (L ++ A :: B :: R) C →
      Unfocused H (L ++ Γ ++ R) C
  | .ldiv A B => ∀ {L Ξ R C}, Unfocused H (L ++ B :: R) C → Unfocused H Ξ A →
      Unfocused H (L ++ Ξ ++ Γ ++ R) C
  | .rdiv B A => ∀ {L Ξ R C}, Unfocused H (L ++ B :: R) C → Unfocused H Ξ A →
      Unfocused H (L ++ Γ ++ Ξ ++ R) C
  | .conj A B =>
      (∀ {L R C}, Unfocused H (L ++ A :: R) C → Unfocused H (L ++ Γ ++ R) C) ∧
      (∀ {L R C}, Unfocused H (L ++ B :: R) C → Unfocused H (L ++ Γ ++ R) C)
  | .disj A B => ∀ {L R C}, Unfocused H (L ++ A :: R) C → Unfocused H (L ++ B :: R) C →
      Unfocused H (L ++ Γ ++ R) C
  | .star A => ∀ {L R C}, (∀ n, Unfocused H (L ++ List.replicate n A ++ R) C) →
      Unfocused H (L ++ Γ ++ R) C
  | .bang A =>
      (∀ {L R C} n, Unfocused H (L ++ List.replicate n A ++ R) C →
        Unfocused H (L ++ Γ ++ R) C) ∧
      (∀ {B}, Unfocused H [A] B → Unfocused H Γ (.bang B))

/-- Commute a cut through the consumer until the designated occurrence is principal. -/
theorem cut_consumer {H : Theory} {T Γ}
    (producer : Unfocused H Γ T) (principal : PrincipalCut H T Γ)
    {Ξ C} (d : Unfocused H Ξ C) :
    ∀ {Δ}, Replace T Γ Ξ Δ → Unfocused H Δ C := by
  induction d with
  | identity p =>
    intro Δ e
    cases e with
    | here => simpa using producer
    | there _ e => cases e
  | tensorL d ih =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .tensorL (ih (h.suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal d
      | there _ h => exact .tensorL (ih ((Replace.there _ (.there _ h)).prepend _))
  | tensorR d₁ d₂ ih₁ ih₂ =>
    intro Δ e
    rcases e.of_append with ⟨Γ', h, rfl⟩ | ⟨Δ', h, rfl⟩
    · exact .tensorR (ih₁ h) d₂
    · exact .tensorR d₁ (ih₂ h)
  | @ldivL L Ξ R A B C d₁ d₂ ih₁ ih₂ =>
    intro Δ e
    rcases e.of_append with ⟨P', h, rfl⟩ | ⟨R', h, rfl⟩
    · rcases h.of_append with ⟨L', hh, rfl⟩ | ⟨Ξ', hh, rfl⟩
      · exact .ldivL (ih₁ (hh.suffix _)) d₂
      · exact .ldivL d₁ (ih₂ hh)
    · cases h with
      | here => simpa [List.append_assoc] using principal d₁ d₂
      | there _ h => exact .ldivL (ih₁ ((Replace.there _ h).prepend _)) d₂
  | ldivR d ih =>
    intro Δ e
    exact .ldivR (ih (.there _ e))
  | @rdivL L Ξ R A B C d₁ d₂ ih₁ ih₂ =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨S', h, rfl⟩
    · exact .rdivL (ih₁ (h.suffix _)) d₂
    · cases h with
      | here => simpa [List.append_assoc] using principal d₁ d₂
      | there _ h =>
        rcases h.of_append with ⟨Ξ', hh, rfl⟩ | ⟨R', hh, rfl⟩
        · exact .rdivL d₁ (ih₂ hh)
        · exact .rdivL (ih₁ ((Replace.there _ hh).prepend _)) d₂
  | rdivR d ih => intro Δ e; exact .rdivR (ih (e.suffix _))
  | zeroL L R C =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .zeroL _ _ _
    · cases h with
      | here => simpa [List.append_assoc] using principal L R C
      | there _ h => exact .zeroL _ _ _
  | oneL d ih =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .oneL (ih (h.suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal d
      | there _ h => exact .oneL (ih (h.prepend _))
  | oneR => intro Δ e; cases e
  | conjL₁ d ih =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .conjL₁ (ih (h.suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal.1 d
      | there _ h => exact .conjL₁ (ih ((Replace.there _ h).prepend _))
  | conjL₂ d ih =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .conjL₂ (ih (h.suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal.2 d
      | there _ h => exact .conjL₂ (ih ((Replace.there _ h).prepend _))
  | conjR d₁ d₂ ih₁ ih₂ => intro Δ e; exact .conjR (ih₁ e) (ih₂ e)
  | disjL d₁ d₂ ih₁ ih₂ =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .disjL (ih₁ (h.suffix _)) (ih₂ (h.suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal d₁ d₂
      | there _ h =>
        exact .disjL (ih₁ ((Replace.there _ h).prepend _))
          (ih₂ ((Replace.there _ h).prepend _))
  | disjR₁ d ih => intro Δ e; exact .disjR₁ (ih e)
  | disjR₂ d ih => intro Δ e; exact .disjR₂ (ih e)
  | starL ds ih =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .starL (fun n => ih n ((h.suffix _).suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal ds
      | there _ h => exact .starL (fun n => ih n (h.prepend _))
  | starR parts ds ih =>
    intro Δ e
    obtain ⟨parts', rfl, hp⟩ := e.flatten_lift (fun Γ => Unfocused H Γ _) parts ds
      (fun Γ hm Δ ed => ih Γ hm ed)
    exact .starR parts' hp
  | bangL n d ih =>
    intro Δ e
    rcases e.of_append with ⟨L', h, rfl⟩ | ⟨R', h, rfl⟩
    · exact .bangL n (ih ((h.suffix _).suffix _))
    · cases h with
      | here => simpa [List.append_assoc] using principal.1 n d
      | there _ h => exact .bangL n (ih (h.prepend _))
  | bangR d ih =>
    intro Δ e
    cases e with
    | here => simpa using principal.2 d
    | there _ e => cases e
  | ncut h d ih =>
    intro Δ e
    rcases e.of_append with ⟨L', hh, rfl⟩ | ⟨R', hh, rfl⟩
    · exact .ncut h (ih (hh.suffix _))
    · exact .ncut h (ih ((Replace.there _ hh).prepend _))

end Focusing


/- ===== Focusing/Continuation.lean ===== -/

namespace Focusing
open Formula Judgment Side

namespace Nonpositive

theorem append {Γ Δ : Context} (hΓ : Nonpositive Γ) (hΔ : Nonpositive Δ) :
    Nonpositive (Γ ++ Δ) := by
  intro A h
  rcases List.mem_append.mp h with h | h
  · exact hΓ A h
  · exact hΔ A h

theorem take_left {Γ Δ : Context} (h : Nonpositive (Γ ++ Δ)) : Nonpositive Γ :=
  fun A hm => h A (List.mem_append_left _ hm)

theorem take_right {Γ Δ : Context} (h : Nonpositive (Γ ++ Δ)) : Nonpositive Δ :=
  fun A hm => h A (List.mem_append_right _ hm)

theorem tail {A Γ} (h : Nonpositive (A :: Γ)) : Nonpositive Γ :=
  fun B hm => h B (List.mem_cons_of_mem _ hm)

theorem singleton {A} (h : A.positive = false) : Nonpositive [A] := by
  simpa [Nonpositive] using h

end Nonpositive

private def ContinuationGoal (H : Theory) (P Q : Context) (A C : Formula) : Judgment → Prop
  | .up L R D _ => D = A → Nonpositive L →
      Focused H (.up (P ++ L) (R ++ Q) C .stored)
  | .left L B R D => D = A → Nonpositive L → Nonpositive R →
      Focused H (.left (P ++ L) B (R ++ Q) C)
  | .right _ _ => True

/-- Extend a derivation by a fixed continuation. The continuation is invoked
only on a right focus with a nonpositive context. All other phases are traversed
by structural induction, including the hypothesis rule and the omega rule. -/
theorem focused_continuation {H : Theory} {P Q : Context} {A C : Formula}
    (nQ : Nonpositive Q)
    (k : ∀ Γ, Nonpositive Γ → Focused H (.right Γ A) →
      Focused H (.up (P ++ Γ ++ Q) [] C .stored))
    {j} (d : Focused H j) : ContinuationGoal H P Q A C j := by
  have finish {Γ} (e : Focused H (.up (P ++ Γ ++ Q) [] C .stored)) :
      Focused H (.up (P ++ Γ) Q C .stored) := by
    simpa using (scan_nonpositive_iff nQ).mpr e
  induction d with
  | identity => trivial
  | tensorL d ih =>
    intro eq nL
    exact .tensorL (ih eq nL)
  | ldivR d ih =>
    intro eq nΓ
    subst A
    exact finish (k _ nΓ (.releaseR rfl (.ldivR d)))
  | rdivR d ih =>
    intro eq nΓ
    subst A
    exact finish (k _ nΓ (.releaseR rfl (.rdivR d)))
  | zeroL => intro _ _; exact .zeroL _ _ _ _
  | oneL d ih => intro eq nL; exact .oneL (ih eq nL)
  | disjL d₁ d₂ ih₁ ih₂ => intro eq nL; exact .disjL (ih₁ eq nL) (ih₂ eq nL)
  | conjR d₁ d₂ ih₁ ih₂ =>
    intro eq nΓ
    subst A
    exact finish (k _ nΓ (.releaseR rfl (.conjR d₁ d₂)))
  | starL ds ih =>
    intro eq nL
    apply Focused.starL
    intro n
    simpa [List.append_assoc] using ih n eq nL
  | tensorR => trivial
  | ldivL d₁ d₂ ih₁ ih₂ =>
    intro eq nL nR
    simpa [List.append_assoc] using Focused.ldivL (ih₁ eq nL.take_left nR) d₂
  | rdivL d₁ d₂ ih₁ ih₂ =>
    intro eq nL nR
    simpa [List.append_assoc] using Focused.rdivL (ih₁ eq nL nR.take_right) d₂
  | oneR => trivial
  | conjL₁ d ih => intro eq nL nR; exact .conjL₁ (ih eq nL nR)
  | conjL₂ d ih => intro eq nL nR; exact .conjL₂ (ih eq nL nR)
  | disjR₁ => trivial
  | disjR₂ => trivial
  | starR => trivial
  | bangL n d ih =>
    intro eq nΓ
    apply finish
    have e := Focused.bangL n (by simpa only [List.append_assoc] using ih eq nΓ.take_left)
    simpa [List.append_assoc] using e
  | bangR d ih =>
    intro eq nΓ
    subst A
    exact finish (k _ nΓ (.releaseR rfl (.storeR rfl (.bangR d))))
  | releaseL hp d ih =>
    intro eq nL nR
    exact .releaseL hp (ih eq nL)
  | releaseR => trivial
  | @storeL L R B D s hp d ih =>
    intro eq nL
    have e := Focused.storeL (L := P ++ L) hp (by simpa only [List.append_assoc] using ih eq (nL.append (.singleton hp)))
    simpa [List.append_assoc] using e
  | storeR hp d ih => intro eq nΓ; exact ih eq nΓ
  | decideL hp d ih =>
    intro eq nΓ
    apply finish
    have e := Focused.decideL hp (ih eq nΓ.take_left nΓ.take_right.tail)
    simpa [List.append_assoc] using e
  | decideR hp d ih =>
    intro eq nΓ
    subst A
    exact finish (k _ nΓ d)
  | decideH hp d ih =>
    intro eq nΓ
    apply finish
    have e := Focused.decideH hp (ih eq nΓ.take_left nΓ.take_right)
    simpa [List.append_assoc] using e

/-- A convenient foc-level form of the continuation lemma. -/
theorem foc_continuation {H : Theory} {P Q Γ : Context} {A C : Formula}
    (nP : Nonpositive P) (nQ : Nonpositive Q) (nc : C.negative = false)
    (k : ∀ Δ, Nonpositive Δ → Focused H (.right Δ A) →
      Focused H (.up (P ++ Δ ++ Q) [] C .stored))
    (d : Focused H (foc Γ A)) : Focused H (foc (P ++ Γ ++ Q) C) := by
  have e := focused_continuation nQ k d rfl (by simp [Nonpositive])
  have e' := (store_right_iff nc).mpr e
  unfold foc
  rw [List.append_assoc]
  apply (scan_nonpositive_iff nP).mpr
  simpa [foc, List.append_assoc] using e'

end Focusing


/- ===== Focusing/Admissibility.lean ===== -/

namespace Focusing
open Formula Judgment Side

theorem foc_to_stored {H : Theory} {Γ C} (nΓ : Nonpositive Γ)
    (nc : C.negative = false) (d : Focused H (foc Γ C)) :
    Focused H (.up Γ [] C .stored) := by
  apply (store_right_iff nc).mp
  exact (scan_nonpositive_iff (L := []) (R := []) nΓ).mp (by simpa [foc] using d)

theorem stored_to_root {H : Theory} {Γ C} (nΓ : Nonpositive Γ)
    (nc : C.negative = false) (d : Focused H (.up Γ [] C .stored)) :
    Focused H (foc Γ C) := by
  have e := (scan_nonpositive_iff (L := []) (R := []) nΓ).mpr (Focused.storeR nc d)
  simpa [foc] using e

private theorem replacement_nonnegs {H : Theory} {T K}
    (nk : Nonpositive K)
    (critical : ∀ {L R C}, Focused H (.left L T R C) →
      Focused H (.up (L ++ K ++ R) [] C .stored))
    {L R C} (nc : C.negative = false)
    (d : Focused H (foc (L ++ T :: R) C)) :
    Focused H (foc (L ++ K ++ R) C) := by
  have eqv := (expand_block_iff (H := H) [] L (K ++ R) [] C .active)
  simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append] at eqv
  try simp only [foc, List.append_assoc, List.nil_append, List.append_nil, List.singleton_append]
  apply eqv.mpr
  intro L' eL
  have eqv := (expand_block_iff (H := H) (L' ++ K) R [] [] C .active)
  simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append] at eqv
  try simp only [foc, List.append_assoc, List.nil_append, List.append_nil, List.singleton_append]
  apply eqv.mpr
  intro R' eR
  have dL := foc_expand_block (P := []) (Γ := L) (R := T :: R) (by simpa using d) eL
  have dR := foc_expand_block (P := L' ++ [T]) (Γ := R) (R := [])
    (by simpa [List.append_assoc] using dL) eR
  have ds : Focused H (foc (L' ++ T :: R') C) := by
    simpa [List.append_assoc] using dR
  cases nt : T.negative with
  | true =>
    exact replace_negative nt nk critical ds
      (.upR ((Replace.here R').prepend L'))
  | false =>
    have e : Focused H (.up L' (T :: R') C .stored) :=
      (store_right_iff nc).mp ((scan_nonpositive_iff eL.nonpositive).mp ds)
    simpa [foc, List.append_assoc] using stored_to_root ((eL.nonpositive.append nk).append eR.nonpositive) nc
      (critical (.releaseL nt e))

/-- Lifting a focused critical case to replacement in an arbitrary foc context. -/
theorem replacement_admissible {H : Theory} {T K}
    (nk : Nonpositive K)
    (critical : ∀ {L R C}, Focused H (.left L T R C) →
      Focused H (.up (L ++ K ++ R) [] C .stored))
    {L R C} (d : Focused H (foc (L ++ T :: R) C)) :
    Focused H (foc (L ++ K ++ R) C) := by
  induction C generalizing L R with
  | atom p => exact replacement_nonnegs nk critical rfl d
  | zero => exact replacement_nonnegs nk critical rfl d
  | one => exact replacement_nonnegs nk critical rfl d
  | tensor A B => exact replacement_nonnegs nk critical rfl d
  | disj A B => exact replacement_nonnegs nk critical rfl d
  | star A => exact replacement_nonnegs nk critical rfl d
  | bang A => exact replacement_nonnegs nk critical rfl d
  | ldiv A B ihA ihB =>
    apply ldiv_right_any_iff.mpr
    exact ihB (L := A :: L) (ldiv_right_any_iff.mp d)
  | rdiv B A ihB ihA =>
    apply rdiv_right_any_iff.mpr
    simpa [List.append_assoc] using ihB (R := R ++ [A])
      (by simpa [List.append_assoc] using rdiv_right_any_iff.mp d)
  | conj A B ihA ihB =>
    exact conj_right_any_iff.mpr
      ⟨ihA (conj_right_any_iff.mp d).1, ihB (conj_right_any_iff.mp d).2⟩

/-- Every normalized hypothesis cut is an instance of contextual replacement. -/
theorem normalized_cut_admissible {H : Theory} {T : Formula} (ht : H T)
    {L R C} (d : Focused H (foc (L ++ T :: R) C)) :
    Focused H (foc (L ++ R) C) := by
  simpa using replacement_admissible (K := []) (by simp [Nonpositive])
    (fun {L R C} e => by simpa using Focused.decideH ht e) d

theorem conj_left₁_admissible {H : Theory} {L R A B C}
    (d : Focused H (foc (L ++ A :: R) C)) :
    Focused H (foc (L ++ conj A B :: R) C) := by
  simpa [List.append_assoc] using replacement_admissible (K := [conj A B])
    (.singleton rfl) (fun {L R C} e => by simpa [List.append_assoc] using Focused.decideL rfl (Focused.conjL₁ (B := B) e)) d

theorem conj_left₂_admissible {H : Theory} {L R A B C}
    (d : Focused H (foc (L ++ B :: R) C)) :
    Focused H (foc (L ++ conj A B :: R) C) := by
  simpa [List.append_assoc] using replacement_admissible (K := [conj A B])
    (.singleton rfl) (fun {L R C} e => by simpa [List.append_assoc] using Focused.decideL rfl (Focused.conjL₂ (A := A) e)) d

theorem ldiv_left_focused_argument {H : Theory} {L Ξ R A B C}
    (nΞ : Nonpositive Ξ) (d : Focused H (foc (L ++ B :: R) C))
    (a : Focused H (.right Ξ A)) :
    Focused H (foc (L ++ Ξ ++ ldiv A B :: R) C) := by
  have e := replacement_admissible (K := Ξ ++ [ldiv A B])
    (nΞ.append (.singleton rfl)) (d := d) (fun {L R C} h => by
      simpa [List.append_assoc] using Focused.decideL rfl (Focused.ldivL h a))
  simpa [List.append_assoc] using e

theorem rdiv_left_focused_argument {H : Theory} {L Ξ R A B C}
    (nΞ : Nonpositive Ξ) (d : Focused H (foc (L ++ B :: R) C))
    (a : Focused H (.right Ξ A)) :
    Focused H (foc (L ++ rdiv B A :: (Ξ ++ R)) C) := by
  have e := replacement_admissible (K := rdiv B A :: Ξ)
    ((Nonpositive.singleton rfl).append nΞ) (d := d) (fun {L R C} h => by
      simpa [List.append_assoc] using Focused.decideL rfl (Focused.rdivL h a))
  simpa [List.append_assoc] using e

private theorem ldiv_left_stable {H : Theory} {L Ξ R A B C}
    (nL : Nonpositive L) (nR : Nonpositive R) (nc : C.negative = false)
    (d : Focused H (foc (L ++ B :: R) C)) (a : Focused H (foc Ξ A)) :
    Focused H (foc (L ++ Ξ ++ ldiv A B :: R) C) := by
  apply foc_continuation nL ((Nonpositive.singleton rfl).append nR) nc (d := a)
  intro Δ nΔ e
  exact foc_to_stored ((nL.append nΔ).append ((Nonpositive.singleton rfl).append nR)) nc
    (ldiv_left_focused_argument nΔ d e)

private theorem rdiv_left_stable {H : Theory} {L Ξ R A B C}
    (nL : Nonpositive L) (nR : Nonpositive R) (nc : C.negative = false)
    (d : Focused H (foc (L ++ B :: R) C)) (a : Focused H (foc Ξ A)) :
    Focused H (foc (L ++ rdiv B A :: (Ξ ++ R)) C) := by
  have e := foc_continuation (nL.append (Nonpositive.singleton (A := rdiv B A) rfl)) nR nc (d := a)
    (fun Δ nΔ e => by
      have h := rdiv_left_focused_argument nΔ d e
      apply foc_to_stored (((nL.append (Nonpositive.singleton (A := rdiv B A) rfl)).append nΔ).append nR) nc
      simpa [List.append_assoc] using h)
  simpa [List.append_assoc] using e

private theorem ldiv_left_nonnegs {H : Theory} {L Ξ R A B C}
    (nc : C.negative = false)
    (d : Focused H (foc (L ++ B :: R) C)) (a : Focused H (foc Ξ A)) :
    Focused H (foc (L ++ Ξ ++ ldiv A B :: R) C) := by
  have eqv := (expand_block_iff (H := H) [] L (Ξ ++ ldiv A B :: R) [] C .active)
  simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append] at eqv
  try simp only [foc, List.append_assoc, List.nil_append, List.append_nil, List.singleton_append]
  apply eqv.mpr
  intro L' eL
  have eqv := (expand_block_iff (H := H) (L' ++ Ξ ++ [ldiv A B]) R [] [] C .active)
  simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append] at eqv
  try simp only [foc, List.append_assoc, List.nil_append, List.append_nil, List.singleton_append]
  apply eqv.mpr
  intro R' eR
  have dL := foc_expand_block (P := []) (Γ := L) (R := B :: R) (by simpa using d) eL
  have dR := foc_expand_block (P := L' ++ [B]) (Γ := R) (R := [])
    (by simpa [List.append_assoc] using dL) eR
  simpa [foc, List.append_assoc] using ldiv_left_stable eL.nonpositive eR.nonpositive nc
    (by simpa [List.append_assoc] using dR) a

private theorem rdiv_left_nonnegs {H : Theory} {L Ξ R A B C}
    (nc : C.negative = false)
    (d : Focused H (foc (L ++ B :: R) C)) (a : Focused H (foc Ξ A)) :
    Focused H (foc (L ++ rdiv B A :: (Ξ ++ R)) C) := by
  have eqv := (expand_block_iff (H := H) [] L (rdiv B A :: (Ξ ++ R)) [] C .active)
  simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append] at eqv
  try simp only [foc, List.append_assoc, List.nil_append, List.append_nil, List.singleton_append]
  apply eqv.mpr
  intro L' eL
  have eqv := (expand_block_iff (H := H) (L' ++ [rdiv B A] ++ Ξ) R [] [] C .active)
  simp only [List.append_assoc, List.nil_append, List.append_nil, List.singleton_append] at eqv
  try simp only [foc, List.append_assoc, List.nil_append, List.append_nil, List.singleton_append]
  apply eqv.mpr
  intro R' eR
  have dL := foc_expand_block (P := []) (Γ := L) (R := B :: R) (by simpa using d) eL
  have dR := foc_expand_block (P := L' ++ [B]) (Γ := R) (R := [])
    (by simpa [List.append_assoc] using dL) eR
  simpa [foc, List.append_assoc] using rdiv_left_stable eL.nonpositive eR.nonpositive nc
    (by simpa [List.append_assoc] using dR) a

theorem ldiv_left_admissible {H : Theory} {L Ξ R A B C}
    (d : Focused H (foc (L ++ B :: R) C)) (a : Focused H (foc Ξ A)) :
    Focused H (foc (L ++ Ξ ++ ldiv A B :: R) C) := by
  induction C generalizing L R with
  | atom p => exact ldiv_left_nonnegs rfl d a
  | zero => exact ldiv_left_nonnegs rfl d a
  | one => exact ldiv_left_nonnegs rfl d a
  | tensor D E => exact ldiv_left_nonnegs rfl d a
  | disj D E => exact ldiv_left_nonnegs rfl d a
  | star D => exact ldiv_left_nonnegs rfl d a
  | bang D => exact ldiv_left_nonnegs rfl d a
  | ldiv D E ihD ihE =>
    apply ldiv_right_any_iff.mpr
    exact ihE (L := D :: L) (ldiv_right_any_iff.mp d)
  | rdiv E D ihE ihD =>
    apply rdiv_right_any_iff.mpr
    simpa [List.append_assoc] using ihE (R := R ++ [D])
      (by simpa [List.append_assoc] using rdiv_right_any_iff.mp d)
  | conj D E ihD ihE =>
    exact conj_right_any_iff.mpr
      ⟨ihD (conj_right_any_iff.mp d).1, ihE (conj_right_any_iff.mp d).2⟩

theorem rdiv_left_admissible {H : Theory} {L Ξ R A B C}
    (d : Focused H (foc (L ++ B :: R) C)) (a : Focused H (foc Ξ A)) :
    Focused H (foc (L ++ rdiv B A :: (Ξ ++ R)) C) := by
  induction C generalizing L R with
  | atom p => exact rdiv_left_nonnegs rfl d a
  | zero => exact rdiv_left_nonnegs rfl d a
  | one => exact rdiv_left_nonnegs rfl d a
  | tensor D E => exact rdiv_left_nonnegs rfl d a
  | disj D E => exact rdiv_left_nonnegs rfl d a
  | star D => exact rdiv_left_nonnegs rfl d a
  | bang D => exact rdiv_left_nonnegs rfl d a
  | ldiv D E ihD ihE =>
    apply ldiv_right_any_iff.mpr
    exact ihE (L := D :: L) (ldiv_right_any_iff.mp d)
  | rdiv E D ihE ihD =>
    apply rdiv_right_any_iff.mpr
    simpa [List.append_assoc] using ihE (R := R ++ [D])
      (by simpa [List.append_assoc] using rdiv_right_any_iff.mp d)
  | conj D E ihD ihE =>
    exact conj_right_any_iff.mpr
      ⟨ihD (conj_right_any_iff.mp d).1, ihE (conj_right_any_iff.mp d).2⟩

end Focusing


/- ===== Focusing/Positive.lean ===== -/

namespace Focusing
open Formula Judgment Side

theorem foc_expand {H : Theory} {Γ Δ A}
    (d : Focused H (foc Γ A)) (e : ExpandsContext Γ Δ) :
    Focused H (foc Δ A) := by
  simpa using foc_expand_block (P := []) (R := []) (by simpa using d) e

theorem tensor_right_admissible {H : Theory} {Γ Δ A B}
    (a : Focused H (foc Γ A)) (b : Focused H (foc Δ B)) :
    Focused H (foc (Γ ++ Δ) (tensor A B)) := by
  have eqv := expand_block_iff (H := H) Γ Δ [] [] (tensor A B) .active
  simp only [List.append_nil] at eqv
  apply eqv.mpr
  intro Δ' eΔ
  have b' := foc_expand b eΔ
  have nΔ := eΔ.nonpositive
  have outer := foc_continuation (P := []) (Q := Δ') (C := tensor A B)
    (by simp [Nonpositive]) nΔ rfl (d := a)
    (fun Ξ nΞ ra => by
      have inner := foc_continuation (P := Ξ) (Q := []) (C := tensor A B)
        nΞ (by simp [Nonpositive]) rfl (d := b')
        (fun Ω nΩ rb => by
          simpa using Focused.decideR rfl (Focused.tensorR ra rb))
      apply foc_to_stored (nΞ.append nΔ) rfl
      simpa using inner)
  simpa [foc] using outer

theorem disj_right₁_admissible {H : Theory} {Γ A B}
    (a : Focused H (foc Γ A)) : Focused H (foc Γ (disj A B)) := by
  simpa using foc_continuation (P := []) (Q := []) (C := disj A B)
    (by simp [Nonpositive]) (by simp [Nonpositive]) rfl
    (fun Δ _ ra => by simpa using Focused.decideR rfl (Focused.disjR₁ (B := B) ra)) a

theorem disj_right₂_admissible {H : Theory} {Γ A B}
    (b : Focused H (foc Γ B)) : Focused H (foc Γ (disj A B)) := by
  simpa using foc_continuation (P := []) (Q := []) (C := disj A B)
    (by simp [Nonpositive]) (by simp [Nonpositive]) rfl
    (fun Δ _ rb => by simpa using Focused.decideR rfl (Focused.disjR₂ (A := A) rb)) b

theorem ExpandsContext.flatten_lift {parts : List Context} {Δ}
    (d : ExpandsContext parts.flatten Δ) :
    ∃ parts' : List Context, parts'.flatten = Δ ∧
      ∀ Γ' ∈ parts', ∃ Γ ∈ parts, ExpandsContext Γ Γ' := by
  induction parts generalizing Δ with
  | nil => cases d; exact ⟨[], rfl, by simp⟩
  | cons Γ parts ih =>
    obtain ⟨Γ', Δ', rfl, hΓ, hΔ⟩ := d.split_append
    obtain ⟨parts', rfl, hp⟩ := ih hΔ
    refine ⟨Γ' :: parts', rfl, ?_⟩
    intro Ξ hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨Γ, by simp, hΓ⟩
    · obtain ⟨Ω, hΩ, eΩ⟩ := hp Ξ hm
      exact ⟨Ω, by simp [hΩ], eΩ⟩

theorem nonpositive_flatten {parts : List Context}
    (h : ∀ Γ ∈ parts, Nonpositive Γ) : Nonpositive parts.flatten := by
  intro A hm
  obtain ⟨Γ, hΓ, hA⟩ := List.mem_flatten.mp hm
  exact h Γ hΓ A hA

/-- Collect any finite family of right focuses using structural continuations. -/
theorem collect_right {H : Theory} {A C : Formula} (nc : C.negative = false)
    (parts : List Context) (np : ∀ Γ ∈ parts, Nonpositive Γ)
    (ds : ∀ Γ ∈ parts, Focused H (foc Γ A)) :
    ∀ P, Nonpositive P →
    (∀ parts' : List Context,
      (∀ Γ ∈ parts', Nonpositive Γ ∧ Focused H (.right Γ A)) →
      Focused H (.up (P ++ parts'.flatten) [] C .stored)) →
    Focused H (.up (P ++ parts.flatten) [] C .stored) := by
  induction parts with
  | nil => intro P nP k; exact k [] (by simp)
  | cons Γ parts ih =>
    intro P nP k
    have npRest : ∀ Δ ∈ parts, Nonpositive Δ := fun Δ hm => np Δ (by simp [hm])
    have dsRest : ∀ Δ ∈ parts, Focused H (foc Δ A) := fun Δ hm => ds Δ (by simp [hm])
    have e := foc_continuation nP (nonpositive_flatten npRest) nc
      (d := ds Γ (by simp)) (fun Ξ nΞ rΞ => by
        apply ih npRest dsRest (P ++ Ξ) (nP.append nΞ)
        intro parts' hp
        have h := k (Ξ :: parts') (by
          intro Ω hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact ⟨nΞ, rΞ⟩
          · exact hp Ω hm)
        simpa [List.append_assoc] using h)
    apply foc_to_stored (nP.append (nonpositive_flatten np)) nc
    simpa [List.append_assoc] using e

theorem star_right_admissible {H : Theory} {A} (parts : List Context)
    (ds : ∀ Γ ∈ parts, Focused H (foc Γ A)) :
    Focused H (foc parts.flatten (star A)) := by
  apply scan_empty_build parts.flatten
  intro Δ eΔ
  obtain ⟨parts', rfl, hp⟩ := eΔ.flatten_lift
  have np : ∀ Γ ∈ parts', Nonpositive Γ := by
    intro Γ hm
    obtain ⟨Ω, hΩ, he⟩ := hp Γ hm
    exact he.nonpositive
  have ds' : ∀ Γ ∈ parts', Focused H (foc Γ A) := by
    intro Γ hm
    obtain ⟨Ω, hΩ, he⟩ := hp Γ hm
    exact foc_expand (ds Ω hΩ) he
  apply Focused.storeR rfl
  exact collect_right rfl parts' np ds' [] (by simp [Nonpositive])
    (fun ps hh => .decideR rfl (.starR ps (fun Γ hm => (hh Γ hm).2)))

private theorem bang_left_nonnegs {H : Theory} {L R A C} (n : Nat)
    (nc : C.negative = false)
    (d : Focused H (foc (L ++ List.replicate n A ++ R) C)) :
    Focused H (foc (L ++ bang A :: R) C) := by
  have eqv := expand_block_iff (H := H) [] L (bang A :: R) [] C .active
  simp only [List.nil_append] at eqv
  apply eqv.mpr
  intro L' eL
  have eqv := expand_block_iff (H := H) (L' ++ [bang A]) R [] [] C .active
  simp only [List.append_nil, List.append_assoc, List.singleton_append] at eqv
  apply eqv.mpr
  intro R' eR
  have dL := foc_expand_block (P := []) (Γ := L) (R := List.replicate n A ++ R)
    (by simpa [List.append_assoc] using d) eL
  have dR := foc_expand_block (P := L' ++ List.replicate n A) (Γ := R) (R := [])
    (by simpa [List.append_assoc] using dL) eR
  have e : Focused H (.up L' (List.replicate n A ++ R') C .stored) :=
    (store_right_iff nc).mp ((scan_nonpositive_iff eL.nonpositive).mp
      (by simpa [foc, List.append_assoc] using dR))
  exact stored_to_root (eL.nonpositive.append ((Nonpositive.singleton rfl).append eR.nonpositive))
    nc (.bangL n e)

theorem bang_left_admissible {H : Theory} {L R A C} (n : Nat)
    (d : Focused H (foc (L ++ List.replicate n A ++ R) C)) :
    Focused H (foc (L ++ bang A :: R) C) := by
  induction C generalizing L R with
  | atom p => exact bang_left_nonnegs n rfl d
  | zero => exact bang_left_nonnegs n rfl d
  | one => exact bang_left_nonnegs n rfl d
  | tensor D E => exact bang_left_nonnegs n rfl d
  | disj D E => exact bang_left_nonnegs n rfl d
  | star D => exact bang_left_nonnegs n rfl d
  | bang D => exact bang_left_nonnegs n rfl d
  | ldiv D E ihD ihE =>
    apply ldiv_right_any_iff.mpr
    exact ihE (L := D :: L) (ldiv_right_any_iff.mp d)
  | rdiv E D ihE ihD =>
    apply rdiv_right_any_iff.mpr
    simpa [List.append_assoc] using ihE (R := R ++ [D])
      (by simpa [List.append_assoc] using rdiv_right_any_iff.mp d)
  | conj D E ihD ihE =>
    exact conj_right_any_iff.mpr
      ⟨ihD (conj_right_any_iff.mp d).1, ihE (conj_right_any_iff.mp d).2⟩

theorem bang_right_admissible {H : Theory} {A B}
    (d : Focused H (foc [A] B)) : Focused H (foc [bang A] (bang B)) :=
  stored_to_root (.singleton rfl) rfl (.bangR d)

end Focusing


/- ===== Focusing/Identity.lean ===== -/

namespace Focusing
open Formula Judgment Side

/-- Identity expansion in ACTMult + H; atomic identity is the only axiom constructor. -/
theorem Unfocused.identity_all (H : Theory) (A : Formula) : Unfocused H [A] A := by
  induction A with
  | atom p => exact .identity p
  | zero => exact .zeroL [] [] zero
  | one => exact .oneL (L := []) (R := []) .oneR
  | tensor A B ihA ihB =>
      exact .tensorL (L := []) (R := []) (.tensorR (Γ := [A]) (Δ := [B]) ihA ihB)
  | ldiv A B ihA ihB =>
      apply Unfocused.ldivR
      exact .ldivL (L := []) (R := []) ihB ihA
  | rdiv B A ihB ihA =>
      apply Unfocused.rdivR
      exact .rdivL (L := []) (R := []) ihB ihA
  | conj A B ihA ihB =>
      exact .conjR (.conjL₁ (L := []) (R := []) ihA)
        (.conjL₂ (L := []) (R := []) ihB)
  | disj A B ihA ihB =>
      exact .disjL (L := []) (R := []) (.disjR₁ ihA) (.disjR₂ ihB)
  | star A ih =>
      apply Unfocused.starL (L := []) (R := [])
      intro n
      have d : Unfocused H (List.replicate n [A]).flatten (star A) := by
        apply Unfocused.starR
        intro Γ hΓ
        have eqΓ : Γ = [A] := (List.mem_replicate.mp hΓ).2
        subst Γ
        exact ih
      simpa using d
  | bang A ih => exact .bangR ih

/-- Hypotheses can be recovered using normalized cuts and identity expansion. -/
theorem Unfocused.hypothesis {H : Theory} {A : Formula} (h : H A) :
    Unfocused H [] A :=
  .ncut (L := []) (R := []) h (Unfocused.identity_all H A)

/-- An atomic canonical identity already has a direct focused proof. -/
theorem canonical_atom_identity (H : Theory) (p : Nat) :
    Focused H (canonical [atom p] (atom p)) := by
  exact .decideR rfl (.identity p)

end Focusing


/- ===== Focusing/Completeness.lean ===== -/

namespace Focusing
open Formula Judgment Side

/-- Unconditional focalization of the calculus with normalized hypothesis cuts. -/
theorem normalized_focusing {H : Theory} {Γ A} (d : Unfocused H Γ A) :
    Focused H (foc Γ A) := by
  induction d with
  | identity p => exact foc_iff_canonical.mpr (canonical_atom_identity H p)
  | tensorL _ ih => exact tensor_left_any_iff.mpr ih
  | tensorR _ _ ih₁ ih₂ => exact tensor_right_admissible ih₁ ih₂
  | ldivL _ _ ih₁ ih₂ => exact ldiv_left_admissible ih₁ ih₂
  | ldivR _ ih => exact ldiv_right_any_iff.mpr ih
  | rdivL _ _ ih₁ ih₂ => exact rdiv_left_admissible ih₁ ih₂
  | rdivR _ ih => exact rdiv_right_any_iff.mpr ih
  | zeroL L R C => exact zero_left_any L R C
  | oneL _ ih => exact one_left_any_iff.mpr ih
  | oneR => exact .storeR rfl (.decideR rfl .oneR)
  | conjL₁ _ ih => exact conj_left₁_admissible ih
  | conjL₂ _ ih => exact conj_left₂_admissible ih
  | conjR _ _ ih₁ ih₂ => exact conj_right_any_iff.mpr ⟨ih₁, ih₂⟩
  | disjL _ _ ih₁ ih₂ => exact disj_left_any_iff.mpr ⟨ih₁, ih₂⟩
  | disjR₁ _ ih => exact disj_right₁_admissible ih
  | disjR₂ _ ih => exact disj_right₂_admissible ih
  | starL _ ih => exact star_left_any_iff.mpr ih
  | starR parts _ ih => exact star_right_admissible parts ih
  | bangL n _ ih => exact bang_left_admissible n ih
  | bangR _ ih => exact bang_right_admissible ih
  | ncut h _ ih => exact normalized_cut_admissible h ih

end Focusing


/- ===== Focusing/Soundness.lean ===== -/

namespace Focusing
open Formula Judgment Side

/-- Erasing focusing gives a proof with normalized cuts. -/
theorem erase {H : Theory} {j : Judgment} (d : Focused H j) :
    Unfocused H j.context j.succedent := by
  induction d with
  | identity p => exact .identity p
  | tensorL _ ih => exact .tensorL ih
  | ldivR _ ih => simpa [Judgment.context, Judgment.succedent] using Unfocused.ldivR ih
  | rdivR _ ih => simpa [Judgment.context, Judgment.succedent] using Unfocused.rdivR ih
  | zeroL L R C s => exact .zeroL L R C
  | oneL _ ih => exact .oneL ih
  | disjL _ _ ih₁ ih₂ => exact .disjL ih₁ ih₂
  | conjR _ _ ih₁ ih₂ =>
      simpa [Judgment.context, Judgment.succedent] using Unfocused.conjR ih₁ ih₂
  | starL _ ih =>
      apply Unfocused.starL
      intro n
      simpa [Judgment.context, Judgment.succedent, List.append_assoc] using ih n
  | tensorR _ _ ih₁ ih₂ => exact .tensorR ih₁ ih₂
  | ldivL _ _ ih₁ ih₂ => exact .ldivL ih₁ ih₂
  | rdivL _ _ ih₁ ih₂ => exact .rdivL ih₁ ih₂
  | oneR => exact .oneR
  | conjL₁ _ ih => exact .conjL₁ ih
  | conjL₂ _ ih => exact .conjL₂ ih
  | disjR₁ _ ih => exact .disjR₁ ih
  | disjR₂ _ ih => exact .disjR₂ ih
  | starR parts _ ih => exact .starR parts ih
  | bangL n _ ih =>
      simpa [Judgment.context, Judgment.succedent] using
        Unfocused.bangL n (by simpa [Judgment.context, Judgment.succedent,
          List.append_assoc] using ih)
  | bangR _ ih =>
      simpa [Judgment.context, Judgment.succedent] using Unfocused.bangR ih
  | releaseL _ _ ih => exact ih
  | releaseR _ _ ih => simpa [Judgment.context, Judgment.succedent] using ih
  | storeL _ _ ih =>
      simpa [Judgment.context, Judgment.succedent, List.append_assoc] using ih
  | storeR _ _ ih => exact ih
  | decideL _ _ ih => simpa [Judgment.context, Judgment.succedent] using ih
  | decideR _ _ ih => simpa [Judgment.context, Judgment.succedent] using ih
  | decideH h _ ih =>
      simpa [Judgment.context, Judgment.succedent] using Unfocused.ncut h ih

/-- A normalized cut is a cut against the corresponding hypothesis. -/
theorem normalized_to_ordinary {H : Theory} {Γ A} (d : Unfocused H Γ A) :
    Ordinary H Γ A := by
  induction d with
  | identity p => exact .identity p
  | tensorL _ ih => exact .tensorL ih
  | tensorR _ _ ih₁ ih₂ => exact .tensorR ih₁ ih₂
  | ldivL _ _ ih₁ ih₂ => exact .ldivL ih₁ ih₂
  | ldivR _ ih => exact .ldivR ih
  | rdivL _ _ ih₁ ih₂ => exact .rdivL ih₁ ih₂
  | rdivR _ ih => exact .rdivR ih
  | zeroL L R C => exact .zeroL L R C
  | oneL _ ih => exact .oneL ih
  | oneR => exact .oneR
  | conjL₁ _ ih => exact .conjL₁ ih
  | conjL₂ _ ih => exact .conjL₂ ih
  | conjR _ _ ih₁ ih₂ => exact .conjR ih₁ ih₂
  | disjL _ _ ih₁ ih₂ => exact .disjL ih₁ ih₂
  | disjR₁ _ ih => exact .disjR₁ ih
  | disjR₂ _ ih => exact .disjR₂ ih
  | starL _ ih => exact .starL ih
  | starR parts _ ih => exact .starR parts ih
  | bangL n _ ih => exact .bangL n ih
  | bangR _ ih => exact .bangR ih
  | ncut h _ ih => simpa using Ordinary.cut (Ordinary.hypothesis h) ih

/-- The fully proved direction of theorem:focusing. -/
theorem focused_sound {H : Theory} {Γ A} (d : Focused H (foc Γ A)) :
    Ordinary H Γ A :=
  normalized_to_ordinary (erase d)

end Focusing


/- ===== Focusing/CutNormalization.lean ===== -/

namespace Focusing
open Formula

/-- Simultaneously replace a finite list of copies, using only cuts on A. -/
theorem cut_copies {H : Theory} {A} (cutA : CutAt H A) (parts : List Context)
    (ds : ∀ Γ ∈ parts, Unfocused H Γ A) {L R C}
    (d : Unfocused H (L ++ List.replicate parts.length A ++ R) C) :
    Unfocused H (L ++ parts.flatten ++ R) C := by
  induction parts generalizing L with
  | nil => simpa using d
  | cons Γ parts ih =>
    have first := cutA (L := L) (R := List.replicate parts.length A ++ R)
      (ds Γ (by simp)) (by simpa [List.append_assoc] using d)
    have rest := ih (fun Δ hm => ds Δ (by simp [hm])) (L := L ++ Γ)
      (by simpa [List.append_assoc] using first)
    simpa [List.append_assoc] using rest

/-- Induction on the producer; principal reductions use only smaller formulas. -/
theorem cut_producer {H : Theory} (T : Formula)
    (smaller : ∀ A, sizeOf A < sizeOf T → CutAt H A)
    {Γ A} (d : Unfocused H Γ A) :
    A = T → ∀ {L R C}, Unfocused H (L ++ T :: R) C →
      Unfocused H (L ++ Γ ++ R) C := by
  induction d with
  | identity p => intro eq L R C e; subst T; simpa [List.append_assoc] using e
  | @tensorL X Y A B D d ih =>
    intro eq L R C e
    have f := ih eq e
    have g := Unfocused.tensorL (L := L ++ X) (R := Y ++ R)
      (by simpa [List.append_assoc] using f)
    simpa [List.append_assoc] using g
  | @tensorR Γ Δ A B da db iha ihb =>
    intro eq L R C e
    subst T
    have ca : CutAt H A := smaller A (by simp [Formula.tensor.sizeOf_spec]; omega)
    have cb : CutAt H B := smaller B (by simp [Formula.tensor.sizeOf_spec]; omega)
    have principal : PrincipalCut H (tensor A B) (Γ ++ Δ) := by
      intro P Q D h
      have f := ca (L := P) (R := B :: Q) da h
      have g := cb (L := P ++ Γ) (R := Q) db (by simpa [List.append_assoc] using f)
      simpa [List.append_assoc] using g
    simpa [List.append_assoc] using cut_consumer (.tensorR da db) principal e ((Replace.here R).prepend L)
  | @ldivL X Ξ Y A B D d a ih iha =>
    intro eq L R C e
    have f := ih eq e
    have g := Unfocused.ldivL (L := L ++ X) (Ξ := Ξ) (R := Y ++ R)
      (by simpa [List.append_assoc] using f) a
    simpa [List.append_assoc] using g
  | @ldivR Γ A B d ih =>
    intro eq L R C e
    subst T
    have ca : CutAt H A := smaller A (by simp [Formula.ldiv.sizeOf_spec]; omega)
    have cb : CutAt H B := smaller B (by simp [Formula.ldiv.sizeOf_spec]; omega)
    have principal : PrincipalCut H (ldiv A B) Γ := by
      intro P Ξ Q D h a
      have f := ca (L := []) (R := Γ) a d
      have g := cb (L := P) (R := Q) f h
      simpa [List.append_assoc] using g
    simpa [List.append_assoc] using cut_consumer (.ldivR d) principal e ((Replace.here R).prepend L)
  | @rdivL X Ξ Y A B D d a ih iha =>
    intro eq L R C e
    have f := ih eq e
    have g := Unfocused.rdivL (L := L ++ X) (Ξ := Ξ) (R := Y ++ R)
      (by simpa [List.append_assoc] using f) a
    simpa [List.append_assoc] using g
  | @rdivR Γ A B d ih =>
    intro eq L R C e
    subst T
    have ca : CutAt H A := smaller A (by simp [Formula.rdiv.sizeOf_spec]; omega)
    have cb : CutAt H B := smaller B (by simp [Formula.rdiv.sizeOf_spec]; omega)
    have principal : PrincipalCut H (rdiv B A) Γ := by
      intro P Ξ Q D h a
      have f := ca (L := Γ) (R := []) a d
      have g := cb (L := P) (R := Q) f h
      simpa [List.append_assoc] using g
    simpa [List.append_assoc] using cut_consumer (.rdivR d) principal e ((Replace.here R).prepend L)
  | zeroL X Y D =>
    intro eq L R C e
    simpa [List.append_assoc] using Unfocused.zeroL (H := H) (L ++ X) (Y ++ R) C
  | @oneL X Y D d ih =>
    intro eq L R C e
    have g := Unfocused.oneL (L := L ++ X) (R := Y ++ R)
      (by simpa [List.append_assoc] using ih eq e)
    simpa [List.append_assoc] using g
  | oneR =>
    intro eq L R C e
    subst T
    have p : PrincipalCut H one [] := by intro P Q D h; simpa using h
    simpa [List.append_assoc] using cut_consumer .oneR p e ((Replace.here R).prepend L)
  | @conjL₁ X Y A B D d ih =>
    intro eq L R C e
    have g := Unfocused.conjL₁ (L := L ++ X) (R := Y ++ R) (B := B)
      (by simpa [List.append_assoc] using ih eq e)
    simpa [List.append_assoc] using g
  | @conjL₂ X Y A B D d ih =>
    intro eq L R C e
    have g := Unfocused.conjL₂ (L := L ++ X) (R := Y ++ R) (A := A)
      (by simpa [List.append_assoc] using ih eq e)
    simpa [List.append_assoc] using g
  | @conjR Γ A B da db iha ihb =>
    intro eq L R C e
    subst T
    have ca : CutAt H A := smaller A (by simp [Formula.conj.sizeOf_spec]; omega)
    have cb : CutAt H B := smaller B (by simp [Formula.conj.sizeOf_spec]; omega)
    have p : PrincipalCut H (conj A B) Γ := ⟨fun h => ca da h, fun h => cb db h⟩
    simpa [List.append_assoc] using cut_consumer (.conjR da db) p e ((Replace.here R).prepend L)
  | @disjL X Y A B D da db iha ihb =>
    intro eq L R C e
    have g := Unfocused.disjL (L := L ++ X) (R := Y ++ R)
      (by simpa [List.append_assoc] using iha eq e)
      (by simpa [List.append_assoc] using ihb eq e)
    simpa [List.append_assoc] using g
  | @disjR₁ Γ A B da iha =>
    intro eq L R C e
    subst T
    have ca : CutAt H A := smaller A (by simp [Formula.disj.sizeOf_spec]; omega)
    have p : PrincipalCut H (disj A B) Γ := fun h _ => ca da h
    simpa [List.append_assoc] using cut_consumer (.disjR₁ da) p e ((Replace.here R).prepend L)
  | @disjR₂ Γ A B db ihb =>
    intro eq L R C e
    subst T
    have cb : CutAt H B := smaller B (by simp [Formula.disj.sizeOf_spec]; omega)
    have p : PrincipalCut H (disj A B) Γ := fun _ h => cb db h
    simpa [List.append_assoc] using cut_consumer (.disjR₂ db) p e ((Replace.here R).prepend L)
  | @starL X Y A D ds ih =>
    intro eq L R C e
    have g := Unfocused.starL (L := L ++ X) (R := Y ++ R) (A := A)
      (fun n => by simpa [List.append_assoc] using ih n eq e)
    simpa [List.append_assoc] using g
  | @starR A parts ds ih =>
    intro eq L R C e
    subst T
    have ca : CutAt H A := smaller A (by simp [Formula.star.sizeOf_spec])
    have p : PrincipalCut H (star A) parts.flatten :=
      fun h => cut_copies ca parts ds (h parts.length)
    simpa [List.append_assoc] using cut_consumer (.starR parts ds) p e ((Replace.here R).prepend L)
  | @bangL X Y A D n d ih =>
    intro eq L R C e
    have g := Unfocused.bangL (L := L ++ X) (R := Y ++ R) (A := A) n
      (by simpa [List.append_assoc] using ih eq e)
    simpa [List.append_assoc] using g
  | @bangR A B d ih =>
    intro eq L R C e
    subst T
    have cb : CutAt H B := smaller B (by simp [Formula.bang.sizeOf_spec])
    have p : PrincipalCut H (bang B) [bang A] := by
      constructor
      · intro P Q D n h
        have f := cut_copies cb (List.replicate n [A]) (by
          intro Γ hm
          have he := List.mem_replicate.mp hm
          simpa [he.2] using d) (by simpa using h)
        have g := Unfocused.bangL (L := P) (R := Q) (A := A) n
          (by simpa using f)
        simpa [List.append_assoc] using g
      · intro D h
        have f := cb (L := []) (R := []) d h
        exact .bangR (by simpa using f)
    simpa [List.append_assoc] using cut_consumer (.bangR d) p e ((Replace.here R).prepend L)
  | @ncut X Y A D h d ih =>
    intro eq L R C e
    have g := Unfocused.ncut (L := L ++ X) (R := Y ++ R) h
      (by simpa [List.append_assoc] using ih eq e)
    simpa [List.append_assoc] using g

/-- Arbitrary cut is admissible in the normalized calculus, even with H and omega. -/
theorem cut_admissible (H : Theory) (A : Formula) : CutAt H A := by
  intro Γ L R C d e
  exact cut_producer A (fun B _ => cut_admissible H B) d rfl e
termination_by sizeOf A

theorem cut_normalization {H : Theory} {Γ A} (d : Ordinary H Γ A) :
    Unfocused H Γ A := by
  induction d with
  | identity p => exact .identity p
  | tensorL _ ih => exact .tensorL ih
  | tensorR _ _ ih₁ ih₂ => exact .tensorR ih₁ ih₂
  | ldivL _ _ ih₁ ih₂ => exact .ldivL ih₁ ih₂
  | ldivR _ ih => exact .ldivR ih
  | rdivL _ _ ih₁ ih₂ => exact .rdivL ih₁ ih₂
  | rdivR _ ih => exact .rdivR ih
  | zeroL L R C => exact .zeroL L R C
  | oneL _ ih => exact .oneL ih
  | oneR => exact .oneR
  | conjL₁ _ ih => exact .conjL₁ ih
  | conjL₂ _ ih => exact .conjL₂ ih
  | conjR _ _ ih₁ ih₂ => exact .conjR ih₁ ih₂
  | disjL _ _ ih₁ ih₂ => exact .disjL ih₁ ih₂
  | disjR₁ _ ih => exact .disjR₁ ih
  | disjR₂ _ ih => exact .disjR₂ ih
  | starL _ ih => exact .starL ih
  | starR parts _ ih => exact .starR parts ih
  | bangL n _ ih => exact .bangL n ih
  | bangR _ ih => exact .bangR ih
  | hypothesis h => exact Unfocused.hypothesis h
  | cut _ _ ih₁ ih₂ => exact cut_admissible H _ ih₁ ih₂

/-- The requested direction, with no mathematical premises besides derivability. -/
theorem focusing_complete {H : Theory} {Γ A} (d : Ordinary H Γ A) :
    Focused H (foc Γ A) := normalized_focusing (cut_normalization d)

/-- Exact full equivalence of theorem:focusing. -/
theorem focusing {H : Theory} {Γ A} :
    Ordinary H Γ A ↔ Focused H (foc Γ A) :=
  ⟨focusing_complete, focused_sound⟩

end Focusing


/- ===== Focusing/Examples.lean ===== -/

namespace Focusing.Examples
open Formula Judgment Side

/-- Empty antecedents are allowed. -/
theorem empty_one (H : Theory) : Focused H (foc [] one) :=
  .storeR rfl (.decideR rfl .oneR)

private theorem ones (H : Theory) (n : Nat) :
    Focused H (.up [] (List.replicate n one) one .active) := by
  induction n with
  | zero => exact empty_one H
  | succ n ih => simpa [List.replicate_succ] using Focused.oneL ih

/-- A genuinely infinitary proof: the premises have unbounded finite depths. -/
theorem star_one (H : Theory) : Focused H (foc [star one] one) := by
  apply Focused.starL
  intro n
  simpa using ones H n

/-- Multiplexing with n = 0. -/
theorem bang_zero_copies (H : Theory) : Focused H (foc [bang one] one) := by
  apply Focused.storeL rfl
  apply Focused.storeR rfl
  apply Focused.bangL 0
  exact .decideR rfl .oneR

/-- A theory formula is inserted under the left focus by decide_H. -/
theorem atomic_hypothesis {H : Theory} {p : Nat} (h : H (atom p)) :
    Focused H (foc [] (atom p)) := by
  apply Focused.storeR rfl
  apply Focused.decideH (L := []) (R := []) h
  apply Focused.releaseL rfl
  apply Focused.storeL rfl
  exact .decideR rfl (.identity p)

/-- A noncommutative left-division application. -/
theorem left_application (H : Theory) (p q : Nat) :
    Focused H (foc [atom p, ldiv (atom p) (atom q)] (atom q)) := by
  apply Focused.storeL rfl
  apply Focused.storeL rfl
  apply Focused.storeR rfl
  apply Focused.decideL (L := [atom p]) (R := []) rfl
  apply Focused.ldivL (L := []) (Ξ := [atom p])
  · apply Focused.releaseL rfl
    apply Focused.storeL rfl
    exact .decideR rfl (.identity q)
  · exact .identity p

end Focusing.Examples


/- ===== Focusing.lean ===== -/

/-! Complete formalization of theorem:focusing for ACTMult with arbitrary simple H. -/


-- Kernel dependency audit of the final results.
#print axioms Focusing.focusing_complete
#print axioms Focusing.focusing
#check @Focusing.focusing_complete
#check @Focusing.focusing
