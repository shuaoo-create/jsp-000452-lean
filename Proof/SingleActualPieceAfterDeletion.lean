import PhysicalSevenSixPrefix
namespace JSP452Audit.StarHost
open SimpleGraph

theorem single_piece_actual_cost {X:Type*} [Finite X] {G:SimpleGraph X} {D:ℕ} (K:DegreeRegion G D)
    (p:↥K.positive) :
    let P := wholePiece G K.barrier p.val
    (G.edgeSet.ncard:ℤ)=((G \ P).edgeSet.ncard:ℤ)+(D:ℤ)*(K.pieceCapacity p:ℤ)+K.pieceWeight p := by
  classical
  intro P
  have account := selected_component_edge_account G K.barrier {p.val} D
  simp only [Finset.sup_singleton,Finset.sum_singleton] at account
  change (P.edgeSet.ncard:ℤ)=(D:ℤ)*(K.pieceCapacity p:ℤ)+K.pieceWeight p at account
  have sum : (G \ P).edgeSet.ncard+P.edgeSet.ncard=G.edgeSet.ncard := by
    rw [edgeSet_sdiff];exact Set.ncard_sdiff_add_ncard_of_subset (edgeSet_subset_edgeSet.mpr (wholePiece_le _ _ _))
  omega

theorem single_piece_actual_row {X:Type*} [Finite X] {G:SimpleGraph X} {D:ℕ} (K:DegreeRegion G D)
    (p:↥K.positive) (A:Set X) {s t r:ℕ} (n m:ℕ→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i<s,0<n i) (pm:∀j<t,0<m j)
    (small:K.pieceCapacity p≤r+A.ncard+1) (row:ForcingRow G s t n m r) :
    ForcingRow ((G \ wholePiece G K.barrier p.val).induce Aᶜ) s t n m (r+A.ncard+K.pieceCapacity p) := by
  classical
  let e : Unit↪(G.induce K.barrierᶜ).ConnectedComponent := ⟨fun _ => p.val,fun _ _ _ => Subsingleton.elim _ _⟩
  let part := fun _:Unit => wholePiece G K.barrier p.val
  let z := fun _:Unit => K.pieceCapacity p
  have costs (T:Finset Unit) : matchingEdges (T.sup part)≤∑i∈T,z i :=
    (component_totals_on_labels G K.barrier e T D).1.le
  have next := actual_piece_menu G A part z n m hn hm pn pm (fun _ => wholePiece_le _ _ _) costs (fun _ => small) row
  simpa [part,z,Finset.univ_unique] using next

#print axioms single_piece_actual_cost
#print axioms single_piece_actual_row
end JSP452Audit.StarHost
