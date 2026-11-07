import SplitCopyOnActualSum
namespace JSP452Audit.StarHost
open SimpleGraph

noncomputable def nonunitOrder {I : Type*} (n : I→ℕ) : ℕ :=
  Nat.card (Vertices (fun i : {i | 2≤n i} => n i.val))

/-- If all nonunit stars landed in the second summand, their distinct
original vertex labels would fit into that summand's order. -/
theorem oversize_nonunit_lands_left {I Y : Type*} [Finite I] [Finite Y]
    (n : I→ℕ) (H : SimpleGraph Y) (U : Set I)
    (right : (forest (fun i:↥(Uᶜ : Set I) => n i.val)).IsContained H)
    (large : Nat.card Y<nonunitOrder n) : ∃i:U,2≤n i.val := by
  by_contra! small
  let big := {i | 2≤n i}
  let idx : ↥big ↪ ↥(Uᶜ : Set I) :=
    ⟨fun i => ⟨i.val,fun mem => (Nat.not_le_of_gt (small ⟨i.val,mem⟩)) i.property⟩,
      fun _ _ eq => Subtype.ext (congrArg (fun z : ↥(Uᶜ : Set I) => z.val) eq)⟩
  let sub := subforestCopy (fun i : big => n i.val) (fun i:↥(Uᶜ : Set I) => n i.val) idx (fun _ => le_rfl)
  obtain ⟨f⟩ := right
  have bound := Nat.card_le_card_of_injective (f.comp sub) (f.comp sub).injective
  exact (Nat.not_le_of_gt large) bound

def oneBinaryHead {l : ℕ} (i : Fin l) : ℕ := if i.val=0 then 2 else 1

theorem oneBinaryHead_antitone (s : ℕ) : Antitone (@oneBinaryHead s) := by
  intro a b le
  have ab : a.val≤b.val := le
  simp only [oneBinaryHead];split_ifs <;> omega

theorem oneBinaryHead_positive {s : ℕ} (i : Fin s) : 1≤oneBinaryHead i := by
  unfold oneBinaryHead;split <;> omega

/-- Select l distinct surviving stars, sending position zero to the
actual surviving nonunit component. Others may be trimmed to one leaf. -/
theorem select_binary_left {I X : Type*} [Fintype I] (G : SimpleGraph X)
    (n : I→ℕ) (pn : ∀i,1≤n i) (l : ℕ) (pos : 0<l) (enough : l≤Fintype.card I)
    (big : ∃i,2≤n i) (copy : (forest n).IsContained G) :
    (forest (@oneBinaryHead l)).IsContained G := by
  classical
  let z : Fin l := ⟨0,pos⟩
  obtain ⟨i,hi⟩ := big
  let f : Fin l ↪ I := (Function.Embedding.nonempty_of_card_le (by simpa using enough)).some
  let g := f.trans (Equiv.swap (f z) i).toEmbedding
  have first : g z=i := by simp [g]
  let sub := subforestCopy (@oneBinaryHead l) n g (fun j => by
    by_cases zero : j.val=0
    · have eq : j=z := Fin.ext zero
      rw [eq,first];exact hi
    · simpa [oneBinaryHead,zero] using pn (g j))
  exact (show (forest (@oneBinaryHead l)).IsContained (forest n) from ⟨sub⟩).trans copy

theorem split_left_has_length {s : ℕ} {Y : Type*} [Finite Y] (n : Fin s→ℕ)
    (pn : ∀i,1≤n i) (H : SimpleGraph Y) (U : Set (Fin s))
    (copy : (forest (fun i:↥(Uᶜ : Set (Fin s)) => n i.val)).IsContained H) :
    s-matchingEdges H≤U.ncard := by
  classical
  let _ := Fintype.ofFinite ↥(Uᶜ : Set (Fin s))
  have rank := forest_copy_matching H (fun i : ↥(Uᶜ : Set (Fin s)) => n i.val) (fun i => pn i.val) copy
  rw [←Nat.card_eq_fintype_card, Nat.card_coe_set_eq,Set.ncard_compl,Nat.card_fin] at rank
  omega

#print axioms oversize_nonunit_lands_left
#print axioms select_binary_left
#print axioms split_left_has_length
end JSP452Audit.StarHost
