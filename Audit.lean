import FocusingComplete

-- Check the complete, universally quantified specification.
example (H : Focusing.Theory) (Γ : Focusing.Context) (A : Focusing.Formula) :
    Focusing.Ordinary H Γ A ↔ Focusing.Focused H (Focusing.root Γ A) :=
  Focusing.focusing

-- These commands fail if the axiom lists change, including if sorryAx appears.
/-- info: 'Focusing.focusing_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Focusing.focusing_complete

/-- info: 'Focusing.focusing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Focusing.focusing
