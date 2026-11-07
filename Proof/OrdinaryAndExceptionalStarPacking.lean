import WhichOriginalLabelsCanBeDamaged
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

/-- Count all vertices of an ordinary star and one named vertex from each
exceptional star, using injectivity of one fixed original forest copy. -/
theorem packed_star_classes {I X : Type*} [Finite I] [Finite X] (H : SimpleGraph X) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy H) (N E : Set I) (apart : Disjoint N E)
    (U V : Set X) (inU : ∀i∈N,∀j : Fin (a+1),f ⟨i,j⟩∈U)
    (exception : ∀i∈E,∃j : Fin (a+1),f ⟨i,j⟩∈V) (sub : V⊆U) :
    E.ncard≤V.ncard ∧ (a+1)*N.ncard+E.ncard≤U.ncard := by
  classical
  let pick (i : E) := (exception i.val i.property).choose
  have spec (i : E) : f ⟨i.val,pick i⟩∈V := (exception i.val i.property).choose_spec
  let sendE (i : E) : V := ⟨f ⟨i.val,pick i⟩,spec i⟩
  have injE : Function.Injective sendE := by
    intro i j eq
    exact Subtype.ext (congrArg Sigma.fst (f.injective (congrArg (fun v : V => v.val) eq)))
  let read : (↥N×Fin (a+1))⊕↥E → Vertices (fun _ : I => a) :=
    Sum.elim (fun z => ⟨z.1.val,z.2⟩) (fun i => ⟨i.val,pick i⟩)
  have dest (z) : f (read z)∈U := by
    rcases z with ⟨i,j⟩|i
    · exact inU i.val i.property j
    · exact sub (spec i)
  let send (z) : U := ⟨f (read z),dest z⟩
  have inj : Function.Injective send := by
    intro z w eq
    have same := f.injective (congrArg (fun v : U => v.val) eq)
    have label := congrArg Sigma.fst same
    have index := congrArg (fun v : Vertices (fun _ : I => a) => v.2.val) same
    rcases z with ⟨i,j⟩|i <;> rcases w with ⟨k,l⟩|k
    · exact congrArg Sum.inl (Prod.ext (Subtype.ext label) (Fin.ext index))
    · change i.val=k.val at label
      exact (Set.disjoint_left.mp apart i.property (label.symm ▸ k.property)).elim
    · change i.val=k.val at label
      exact (Set.disjoint_left.mp apart (label.symm ▸ k.property) i.property).elim
    · exact congrArg Sum.inr (Subtype.ext label)
  have bound := Nat.card_le_card_of_injective send inj
  rw [Nat.card_sum,Nat.card_prod,Nat.card_fin] at bound
  simpa only [Nat.card_coe_set_eq,Nat.mul_comm N.ncard] using
    And.intro (Nat.card_le_card_of_injective sendE injE) bound

#print axioms packed_star_classes
end JSP452Audit.StarHost
