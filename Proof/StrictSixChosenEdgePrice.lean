import PhysicalSixColumnEdgeAccount
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_price_from_sixth (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) (M:ℕ)
    (sixth:widthAt F.n F.m F.r 6≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) 6+M) :
    let P := matchingEdges (F.G.induce (componentVertices F.G T))
    let d := F.rank-matchingEdges F.G
    5*P+3*T.card+1≤d+highestWidth F.n F.m F.r+4*(P+(T.card-1)/2)+M := by
  intro P d
  let K := P+(T.card-1)/2
  let tax (j:ℕ) := if j=6 then M else K
  have general := (strict_six_chosen_component_columns F paid six T actual).2.2
  have price (j:ℕ) (lo:2≤j) (_:j≤6) : widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+tax j := by
    by_cases eq : j=6
    · subst j;simpa [tax] using sixth
    · simpa [tax,eq,K,P] using general j (by omega)
  have total := six_column_edge_account F paid six T actual tax price
  have sum : (∑q∈Finset.range 5,tax (q+2))=4*K+M := by
    simp [Finset.sum_range_succ,tax];omega
  change 5*P+3*T.card+1≤d+highestWidth F.n F.m F.r+_ at total
  rw [sum] at total
  omega

theorem strict_six_chosen_edge_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) :
    let P := matchingEdges (F.G.induce (componentVertices F.G T))
    let K := P+(T.card-1)/2
    let d := F.rank-matchingEdges F.G
    let h := highestWidth F.n F.m F.r
    let M2 := chosenSlots F.G T 2
    let M3 := chosenSlots F.G T 3
    (h≤T.card+1 → 5*P+3*T.card+1≤d+h+4*K+M2) ∧
    ((∀i,F.n i≤4) → (∀j,F.m j≤4) → 5*P+3*T.card+1≤d+h+4*K+M3+(h-1)) := by
  intro P K d h M2 M3
  let E := uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) 6
  obtain ⟨global,both⟩ := strict_sixth_column_by_slots F paid six T
  change widthAt F.n F.m F.r 6≤E+max M2 (M3+(h-1)) at global
  have saving := six_slot_saving_per_piece F paid six T actual
  change M3+T.card≤M2 at saving
  constructor
  · intro plenty
    have sixth : widthAt F.n F.m F.r 6≤E+M2 := by omega
    exact strict_six_price_from_sixth F paid six T actual M2 sixth
  · intro red blue
    have sixth := both red blue
    change widthAt F.n F.m F.r 6≤E+M3+(h-1) at sixth
    have squeeze := strict_six_price_from_sixth F paid six T actual (M3+(h-1)) (by
      change widthAt F.n F.m F.r 6≤E+(M3+(h-1));omega)
    change 5*P+3*T.card+1≤d+h+4*K+(M3+(h-1)) at squeeze
    omega

#print axioms strict_six_price_from_sixth
#print axioms strict_six_chosen_edge_price
end JSP452Audit.StarHost
