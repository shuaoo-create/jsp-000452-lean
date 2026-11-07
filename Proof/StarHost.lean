import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.StarHost
open SimpleGraph
variable {I : Type*} (n : I → ℕ)

abbrev Vertices := Σ i : I, Fin (n i + 1)
abbrev Leaves := Σ i : I, Fin (n i)

/-- This is the explicit disjoint star union in the pinned original target. -/
def forest : SimpleGraph (Vertices n) := fromRel (fun u v =>
  u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0))

def center (i : I) : Vertices n := ⟨i,0⟩
def leaf (p : Leaves n) : Vertices n := ⟨p.1,p.2.succ⟩

theorem leaf_ne_center (p : Leaves n) (i : I) : leaf n p ≠ center n i := by
  intro eq
  have val := congrArg (fun z : Vertices n => z.2.val) eq
  simp [leaf,center] at val

private theorem leaf_injective : Function.Injective (leaf n) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  have owners : i = j := congrArg Sigma.fst eq
  subst j
  have val := congrArg (fun z : Vertices n => z.2.val) eq
  simp [leaf] at val
  exact congrArg (Sigma.mk i) (Fin.ext val)

theorem starEdge (p : Leaves n) : (forest n).Adj (center n p.1) (leaf n p) :=
  ⟨(leaf_ne_center n p p.1).symm,Or.inl ⟨rfl,Or.inl rfl⟩⟩

def edgeOfLeaf (p : Leaves n) : (forest n).edgeSet :=
  ⟨s(center n p.1,leaf n p), (forest n).mem_edgeSet.mpr (starEdge n p)⟩

private theorem edge_injective : Function.Injective (edgeOfLeaf n) := by
  intro a b h
  have e := congrArg Subtype.val h
  change s(center n a.1,leaf n a) = s(center n b.1,leaf n b) at e
  rcases Sym2.eq_iff.mp e with ⟨_,same⟩ | ⟨_,bad⟩
  · exact leaf_injective n same
  · exact (leaf_ne_center n a b.1 bad).elim

private theorem centered {i : I} (a b : Fin (n i + 1)) (hne : a ≠ b)
    (hz : a.val = 0 ∨ b.val = 0) :
    ∃ p : Leaves n, (edgeOfLeaf n p).val = s((⟨i,a⟩ : Vertices n),⟨i,b⟩) := by
  rcases hz with ha | hb
  · have origin : a = 0 := Fin.ext ha
    subst a
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr (Ne.symm hne)
    exact ⟨⟨i,j⟩,rfl⟩
  · have origin : b = 0 := Fin.ext hb
    subst b
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hne
    exact ⟨⟨i,j⟩,Sym2.eq_swap⟩

private theorem edge_surjective : Function.Surjective (edgeOfLeaf n) := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨i,a⟩ := x
    obtain ⟨j,b⟩ := y
    have adj := (forest n).mem_edgeSet.mp he
    rcases adj with ⟨notEq,⟨owner,hz⟩ | ⟨owner,hz⟩⟩
    · change i = j at owner
      subst j
      obtain ⟨p,h⟩ := centered n a b (fun eq => notEq (congrArg (Sigma.mk i) eq)) hz
      exact ⟨p,Subtype.ext h⟩
    · change j = i at owner
      subst j
      obtain ⟨p,h⟩ := centered n a b (fun eq => notEq (congrArg (Sigma.mk i) eq)) hz.symm
      exact ⟨p,Subtype.ext h⟩

noncomputable def edgeEquiv : Leaves n ≃ (forest n).edgeSet :=
  Equiv.ofBijective _ ⟨edge_injective n,edge_surjective n⟩

theorem edge_count [Fintype I] : Nat.card (forest n).edgeSet = ∑ i, n i := by
  rw [← Nat.card_congr (edgeEquiv n)]
  simp [Leaves]

#print axioms edge_count
end JSP452Audit.StarHost
