import SignedEighthColumnOnFirstStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_signed_first_stage_on_exterior (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (H:EightSevenSixHistory (F.G.induce (componentVertices F.G T)ᶜ)) :
    let U := componentVertices F.G T
    let O := F.G.induce Uᶜ
    let P := ∑c∈T,Nat.card c.supp/2
    let b := H.eight.ncard
    let L := widthAt F.n F.m F.r 8
    let h := highestWidth F.n F.m F.r
    L-b≤min (P-T.card) (2*P-7*T.card)+(22+2*h)/5-2 ∧
      minimumExposure (O.induce H.eightᶜ) 7≤(22+2*h)/5 := by
  intro U O P b L h
  obtain ⟨A,first,small⟩ := short_stages_on_odd_regular_components F.G 4 (by decide) T actual
  change A.ncard+T.card≤P at small
  have missing := eight_outside_each_independent_piece F.G T actual A first.1
  have orders := (regular_union_at_even_degree F.G 4 T actual).1
  change (componentVertices F.G T).ncard=2*P+T.card at orders
  have bound : A.ncard≤min (P-T.card) (2*P-7*T.card) := by omega
  have closed := component_vertices_closed F.G T
  obtain ⟨whole,count⟩ := join_closed_degree_stages F.G U 8 closed A H.eight first H.first
  let S := Subtype.val '' A∪Subtype.val '' H.eight
  change S.ncard=A.ncard+b at count
  have proof := strict_eight_signed_first_residual F paid eight S whole
  change minimumExposure (F.G.induce Sᶜ) 7≤(22+2*h)/5 ∧ L-S.ncard≤(22+2*h)/5-2 at proof
  have exp := exposure_after_closed_stage_split F.G U closed A H.eight 7
  change minimumExposure (F.G.induce Sᶜ) 7=minimumExposure ((F.G.induce U).induce Aᶜ) 7+minimumExposure (O.induce H.eightᶜ) 7 at exp
  omega

#print axioms strict_signed_first_stage_on_exterior
end JSP452Audit.StarHost
