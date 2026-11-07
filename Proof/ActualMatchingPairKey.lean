import PairedNeighborhoodProbability
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V]

/-- Encode every vertex by a coordinate and one of its two labels. Endpoints
of the given actual matching share a coordinate and have opposite labels. -/
theorem actual_matching_pair_key (H : SimpleGraph V) (M : H.Subgraph) (hm : M.IsMatching) :
    ∃key : V ↪ V×Bool,∀v∈M.verts,∃w,M.Adj v w ∧ (key v).1=(key w).1 ∧ (key v).2≠(key w).2 := by
  classical
  let _ := Fintype.ofFinite V
  let mate (v:V) := if hv:v∈M.verts then (hm hv).choose else v
  have hit (v:V) (hv:v∈M.verts) : M.Adj v (mate v) := by
    dsimp [mate];rw [dif_pos hv];exact (hm hv).choose_spec.1
  have inv (v:V) : mate (mate v)=v := by
    by_cases hv:v∈M.verts
    · have edge := hit v hv
      exact hm.eq_of_adj_left (hit (mate v) (M.edge_vert edge.symm)) edge.symm
    have fixed : mate v=v := dif_neg hv
    rw [fixed,fixed]
  let label := Fintype.equivFin V
  let encode (v:V) : V×Bool := if label (mate v)<label v then (mate v,true) else (v,false)
  let decode (p:V×Bool) := if p.2 then mate p.1 else p.1
  have back (v:V) : decode (encode v)=v := by
    by_cases side : label (mate v)<label v <;> simp [encode,decode,side,inv]
  let key : V ↪ V×Bool := ⟨encode,fun v w eq => (back v).symm.trans ((congrArg decode eq).trans (back w))⟩
  refine ⟨key,?_⟩
  intro v hv
  have edge := hit v hv
  have ne : label v≠label (mate v) := fun eq => edge.ne (label.injective eq)
  refine ⟨mate v,edge,?_⟩
  change (encode v).1=(encode (mate v)).1 ∧ (encode v).2≠(encode (mate v)).2
  rcases lt_or_gt_of_ne ne with lt|gt
  · simp [encode,lt,lt.not_gt,inv]
  · simp [encode,gt,gt.not_gt,inv]

/-- If two neighbours carry distinct labels of the same coordinate that
coordinate has both of its labels in the closed neighbourhood. -/
theorem neighboring_pair_has_two_sides {I : Type*} (key : V ↪ I×Bool) (N : Set V)
    {v w : V} (inV : v∈N) (inW : w∈N) (owner : (key v).1=(key w).1) (diff : (key v).2≠(key w).2) :
    (pairSidesAt key N (key v).1).card=2 := by
  let S := pairSidesAt key N (key v).1
  have a : (key v).2∈S := (mem_pair_sides _ _ _ _).2 ⟨v,inV,rfl⟩
  have b : (key w).2∈S := (mem_pair_sides _ _ _ _).2 ⟨w,inW,by rw [owner]⟩
  have low : 1<S.card := Finset.one_lt_card.mpr ⟨_,a,_,b,diff⟩
  have high : S.card≤2 := (Finset.card_le_univ S).trans (by decide)
  change S.card=2;omega

#print axioms actual_matching_pair_key
#print axioms neighboring_pair_has_two_sides
end JSP452Audit.StarHost
