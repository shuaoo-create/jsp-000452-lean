import AThirdGapWouldForceExactlyOneActualOriginalOddRegularComponent
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure RegularOddBlock {X:Type u} [Finite X] (G:SimpleGraph X) (p:ℕ) where
  piece : G.ConnectedComponent
  full : piece∈oddRegularComponents G (2*p)

namespace RegularOddBlock
variable {X:Type u} [Finite X] {G:SimpleGraph X} {p:ℕ} (B:RegularOddBlock G p)
abbrev inside := B.piece.toSimpleGraph
abbrev outside := G.induce B.piece.suppᶜ
noncomputable abbrev P := Nat.card B.piece.supp/2

theorem original_geometry :
    p≤B.P ∧ Nat.card B.piece.supp=2*B.P+1 ∧ matchingEdges B.inside≤B.P ∧
    G.edgeSet.ncard=B.outside.edgeSet.ncard+(2*p)*B.P+p ∧
    matchingEdges G=matchingEdges B.outside+matchingEdges B.inside := by
  have reg (v:B.piece.supp) : Nat.card (B.inside.neighborSet v)=2*p :=
    (component_degree_eq G B.piece v).trans (B.full.2 _ v.property)
  have size := odd_regular_order_edge_count B.inside p B.full.1 reg
  have first := half_order_of_regular_component B.inside p B.piece.nonempty_supp.to_subtype.some (reg _)
  have rank := regular_exposure_order_rank B.inside (2*p) reg
  have sep := component_exterior_iso G B.piece
  have edge : G.edgeSet.ncard=B.inside.edgeSet.ncard+B.outside.edgeSet.ncard := by
    rw [←edge_ncard_sumGraph];exact (Nat.card_congr sep.mapEdgeSet).symm
  have part := rank_eq_of_graph_iso sep
  rw [matchingEdges_sumGraph] at part
  obtain ⟨order,cost⟩ := size
  change Nat.card B.piece.supp=2*B.P+1 at order
  change B.inside.edgeSet.ncard=(2*p)*B.P+p at cost
  change 2*matchingEdges B.inside+minimumExposure B.inside (2*p)=Nat.card B.piece.supp at rank
  rw [order] at rank
  change matchingEdges B.inside+matchingEdges B.outside=matchingEdges G at part
  exact ⟨first,order,by omega,by omega,by omega⟩

theorem original_row {s t r:ℕ} (n m:ℕ→ℕ) (row:ForcingRow G s t n m r) :
    ForcingRow (B.outside⊕g B.inside) s t n m r := by
  exact forcingRow_of_iso ((component_exterior_iso G B.piece).symm.trans (Iso.sumComm (G:=B.inside) (H:=B.outside))) row

end RegularOddBlock

theorem conservative_sum_menu {A B:Type u} [Finite A] [Finite B] (O:SimpleGraph A) (C:SimpleGraph B)
    {s t r:ℕ} (n m:ℕ→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀j<s,0<n j) (pm:∀j<t,0<m j)
    (P:ℕ) (rank:matchingEdges C≤P) (small:P≤r+1) (row:ForcingRow (O⊕g C) s t n m r) :
    ForcingRow O s t n m (r+P) := by
  classical
  let part (_:Fin 1) := (⊥:SimpleGraph A)⊕g C
  let Y := O⊕g (⊥:SimpleGraph B)
  let z (_:Fin 1) := P
  have sub (x:Fin 1) : part x≤O⊕g C := by
    rintro (a|a) (b|b) e
    · exact e.elim
    all_goals exact e
  have out : Y≤O⊕g C := by
    rintro (a|a) (b|b) e
    · exact e
    · exact e
    · exact e
    · exact e.elim
  have cover : O⊕g C≤Y⊔Finset.univ.sup part := by
    rintro (a|a) (b|b) e
    · exact Or.inl e
    · exact Or.inl e
    · exact Or.inl e
    · exact Or.inr ((Finset.le_sup (f:=part) (Finset.mem_univ (0:Fin 1))) (show (part 0).Adj (Sum.inr a) (Sum.inr b) from e))
  have cost (T:Finset (Fin 1)) : matchingEdges (T.sup part)≤∑x∈T,z x := (subfamily_rank_le_sum part T).trans
    (Finset.sum_le_sum (fun x _ => by change matchingEdges ((⊥:SimpleGraph A)⊕g C)≤P;simpa only [matchingEdges_sumGraph,matchingEdges_bot,Nat.zero_add] using rank))
  have next := realized_capacity_menu_row _ Y part z n m hn hm out sub cover cost (split_capacities_of_small z r (fun _ => small)) row
  have total : (∑x:Fin 1,z x)=P := by simp [z]
  rw [total] at next
  exact remove_isolated_summand_row O n m pn pm next

theorem regular_block_exterior_menu {X:Type u} [Finite X] {G:SimpleGraph X} {p:ℕ} (B:RegularOddBlock G p)
    {s t r:ℕ} (n m:ℕ→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀j<s,0<n j) (pm:∀j<t,0<m j)
    (row:ForcingRow G s t n m r) (U:Set ↥(B.piece.suppᶜ:Set X)) (small:B.P≤r+U.ncard+1) :
    ForcingRow (B.outside.induce Uᶜ) s t n m (r+U.ncard+B.P) := by
  have real := delete_only_from_left_summand _ B.inside U n m hn hm pn pm (B.original_row n m row)
  exact conservative_sum_menu _ _ n m hn hm pn pm B.P B.original_geometry.2.2.1 small real

#print axioms RegularOddBlock.original_geometry
#print axioms RegularOddBlock.original_row
#print axioms conservative_sum_menu
#print axioms regular_block_exterior_menu
end JSP452Audit.StarHost
