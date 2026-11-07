import RetainActualSixthColumnColors
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_no_five_exterior_full_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4)
    (T:Finset F.G.ConnectedComponent) (A:Set (componentVertices F.G T))
    (B:Set ↥((componentVertices F.G T)ᶜ:Set F.X))
    (inside:CompleteDegreeStage (F.G.induce (componentVertices F.G T)) 6 A)
    (outside:CompleteDegreeStage (F.G.induce (componentVertices F.G T)ᶜ) 6 B) :
    A.ncard+B.ncard=widthAt F.n F.m F.r 6 ∧ A.ncard≤chosenSlots F.G T 3 ∧
      widthAt F.n F.m F.r 6≤B.ncard+chosenSlots F.G T 3 := by
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let L := widthAt F.n F.m F.r 6
  let M := chosenSlots F.G T 3
  let S := (Subtype.val '' A)∪(Subtype.val '' B)
  have closed := component_vertices_closed F.G T
  obtain ⟨joined,size⟩ := join_closed_degree_stages F.G U 6 closed A B inside outside
  obtain ⟨exactSize,limit⟩ := strict_single_six_no_five_rigidity F paid six red blue S joined
  change S.ncard=A.ncard+B.ncard at size
  change S.ncard=L at exactSize
  rw [exposure_after_closed_stage_split F.G U closed A B 5] at limit
  have upper : minimumExposure (O.induce Bᶜ) 5≤2 := by change _+minimumExposure (O.induce Bᶜ) 5≤2 at limit;omega
  have cap (v:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤6 := (induced_neighbor_count_le F.G Uᶜ v).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq six)
  have avail (v) : Nat.card ((O.induce Bᶜ).neighborSet v)≤5 := by
    have := complete_stage_lowers_cap O 6 B cap outside v;omega
  have typed := strict_single_six_no_five_typed F paid six red blue T
  have lower : ExactTypedWidth (O.induce Bᶜ) 4 3 (L-M-B.ncard) ∨ ExactTypedWidth (O.induce Bᶜ) 3 4 (L-M-B.ncard) := by
    rcases typed with rb|br
    · exact Or.inr (typed_width_after_deletion O B (by decide : 0<3) (by decide : 0<4) rb)
    · exact Or.inl (typed_width_after_deletion O B (by decide : 0<4) (by decide : 0<3) br)
  have bound := sharp_five_from_typed_width (O.induce Bᶜ) avail (L-M-B.ncard) lower
  change A.ncard+B.ncard=L ∧ A.ncard≤M ∧ L≤B.ncard+M
  clear * - upper exactSize size bound
  refine ⟨by omega,by omega,by omega⟩

#print axioms strict_no_five_exterior_full_stage
end JSP452Audit.StarHost
