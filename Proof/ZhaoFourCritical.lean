import ZhaoFourComplement

namespace JSP452Audit.StarHost
open SimpleGraph
private abbrev V := ZhaoVertex 2
private abbrev C := (zhaoGraph 2)ᶜ
private abbrev L (i : Fin 4) : V := zhaoLeft i
private abbrev R (i : Fin 4) : V := zhaoRight i

/-- Both pairs in an intact four-vertex side. -/
private def intact (side : Fin 4 → V) : Finset (Sym2 V) :=
  {s(side 0,side 1),s(side 2,side 3)}

/-- Pair the center with a surviving upper label of the damaged side,
and pair its two remaining vertices with each other. -/
private def repaired (side : Fin 4 → V) (deleted : Fin 4) : Finset (Sym2 V) :=
  if deleted=0 then {s(none,side 2),s(side 1,side 3)}
  else if deleted=1 then {s(none,side 2),s(side 0,side 3)}
  else if deleted=2 then {s(none,side 3),s(side 0,side 1)}
  else {s(none,side 2),s(side 0,side 1)}

private def survivingPairs : V → Finset (Sym2 V)
  | none => intact L ∪ intact R
  | some (.inl i) => repaired L i ∪ intact R
  | some (.inr i) => intact L ∪ repaired R i

private theorem validPair : ∀ v y z : V, s(y,z) ∈ survivingPairs v → C.Adj y z := by decide

private theorem partnerExists : ∀ v y : V, y≠v → ∃ z : V, z≠v ∧ s(y,z)∈survivingPairs v := by
  decide

set_option maxHeartbeats 1500000 in
private theorem partnerUnique : ∀ v y z w : V,
    s(y,z)∈survivingPairs v → s(y,w)∈survivingPairs v → z=w := by decide

/-- A genuine perfect matching of each of the nine actual induced graphs
obtained by deletion, with the displayed four pairs as its edges. -/
theorem zhao_four_complement_critical : PerfectAfterEveryDeletion (zhaoGraph 2)ᶜ := by
  intro v
  let H := C.induce {y | y ≠ v}
  let M : H.Subgraph := {
    verts := Set.univ
    Adj x y := s(x.val,y.val)∈survivingPairs v
    adj_sub := fun {x y} h => validPair v x.val y.val h
    edge_vert := fun {_ _} _ => Set.mem_univ _
    symm := ⟨fun _ _ h => Sym2.eq_swap ▸ h⟩ }
  refine ⟨M,Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro y
  obtain ⟨z,alive,edge⟩ := partnerExists v y.val y.property
  exact ⟨⟨z,alive⟩,edge,fun w second => Subtype.ext (partnerUnique v y.val w.val z second edge)⟩

#print axioms zhao_four_complement_critical
end JSP452Audit.StarHost
