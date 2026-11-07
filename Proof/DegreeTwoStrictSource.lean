import UniversalSelector
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
/-- Either original head is bounded by the actual critical full degree. If
it were one larger, the opposite legal corner would be an attaining unit. -/
theorem minimal_original_head_cap (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    (∀ i, F.n i≤D) ∧ (∀ j, F.m j≤D) := by
  intro D
  obtain ⟨_,_,_,_,_,heads⟩ := minimal_rank_exact_source F paid
  obtain ⟨sr,tr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  let i0 : Fin F.s := ⟨0,F.hs⟩
  let j0 : Fin F.t := ⟨0,F.ht⟩
  let ir : Fin F.s := ⟨F.r,by omega⟩
  let jr : Fin F.t := ⟨F.r,by omega⟩
  have red : F.n i0≤D := by
    have index : i0.val+jr.val=F.r := Nat.zero_add _
    have ant := antiDiag_member F.n F.m i0 jr
    rw [index] at ant
    have minB := F.pm jr
    by_contra! le
    have attained : diagonal F.n F.m (F.r+2)=F.n i0+F.m jr-1 := by dsimp [D] at le; omega
    have b := (heads i0 jr index attained).2
    dsimp [D] at le
    omega
  have blue : F.m j0≤D := by
    have index : ir.val+j0.val=F.r := rfl
    have ant := antiDiag_member F.n F.m ir j0
    rw [index] at ant
    have minA := F.pn ir
    by_contra! le
    have attained : diagonal F.n F.m (F.r+2)=F.n ir+F.m j0-1 := by dsimp [D] at le; omega
    have a := (heads ir j0 index attained).1
    dsimp [D] at le
    omega
  exact ⟨fun i => (F.hn (show i0 ≤ i from Nat.zero_le _)).trans red,
    fun j => (F.hm (show j0 ≤ j from Nat.zero_le _)).trans blue⟩

/-- Degree at most two in the normalized branch forces degree exactly two,
and both original lists have a genuine two-leaf star; all remaining demands
are either one or two, before any suffix is cut. -/
theorem degree_two_binary_source (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (small : diagonal F.n F.m (F.r+2)-1≤2) :
    diagonal F.n F.m (F.r+2)=3 ∧ (∀ i, F.n i=1 ∨ F.n i=2) ∧ (∀ j, F.m j=1 ∨ F.m j=2) ∧
      ∃ (i : Fin F.s) (j : Fin F.t), i.val+j.val=F.r ∧ F.n i=2 ∧ F.m j=2 := by
  obtain ⟨_,_,_,_,_,heads⟩ := minimal_rank_exact_source F paid
  have ⟨red,blue⟩ := minimal_original_head_cap F paid
  obtain ⟨i,j,idx,att⟩ := diagonal_attained F.n F.m F.hs F.ht F.r (by have h:=F.live; dsimp [rowCount] at h; omega)
  have ⟨ni,mj⟩ := heads i j idx att
  refine ⟨by omega,fun k => ?_,fun k => ?_,i,j,idx,by omega,by omega⟩
  · have lo := F.pn k; have hi := red k; omega
  · have lo := F.pm k; have hi := blue k; omega
#print axioms minimal_original_head_cap
#print axioms degree_two_binary_source
end JSP452Audit.StarHost