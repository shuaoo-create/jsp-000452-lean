import SingleFiveHeadStageEquality
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem single_six_stage_minimum_size (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (mem:c∈oddRegularComponents F.G 6)
    (A:Set c.supp) (inside:CompleteDegreeStage c.toSimpleGraph 6 A) :
    matchingEdges c.toSimpleGraph≤A.ncard+1 := by
  obtain ⟨B,out⟩ := complete_degree_stage_exists (F.G.induce c.suppᶜ) 6
  have exactL := single_five_head_shadow_exact F paid six c mem B out
  have closed : ∀x∈c.supp,∀y,F.G.Adj x y → y∈c.supp := fun _ hx _ e => (c.mem_supp_congr_adj e).mp hx
  have bound := strict_six_shadow_on_actual_exterior F paid six c.supp closed A B inside out
  have h := (strict_six_only_one_original_component F paid six).1
  rw [exactL,h] at bound
  omega

theorem last_six_residual_certificate (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (mem:c∈oddRegularComponents F.G 6)
    (B:Set ↥(c.suppᶜ:Set F.X)) (out:CompleteDegreeStage (F.G.induce c.suppᶜ) 6 B) :
    ∃A:Set c.supp,let S := Subtype.val '' A∪Subtype.val '' B
      CompleteDegreeStage c.toSimpleGraph 6 A ∧ A.ncard+1=matchingEdges c.toSimpleGraph ∧
      CompleteDegreeStage F.G 6 S ∧ S.ncard+4=widthAt F.n F.m F.r 6 ∧
      minimumExposure (F.G.induce Sᶜ) 5=4 ∧ minimumExposure ((F.G.induce c.suppᶜ).induce Bᶜ) 5≤4 := by
  obtain ⟨_,ord,_,edges⟩ := strict_six_true_component_capacity F paid six c mem
  have reg (v:c.supp) := (component_degree_eq F.G c v).trans (mem.2 v.val v.property)
  obtain ⟨A,inside,short⟩ := short_stage_odd_six_regular c.toSimpleGraph _ reg ord edges
  have minSize := single_six_stage_minimum_size F paid six c mem A inside
  have exactL := single_five_head_shadow_exact F paid six c mem B out
  have closed : ∀x∈c.supp,∀y,F.G.Adj x y → y∈c.supp := fun _ hx _ e => (c.mem_supp_congr_adj e).mp hx
  obtain ⟨global,number⟩ := join_closed_degree_stages F.G c.supp 6 closed A B inside out
  let S := Subtype.val '' A∪Subtype.val '' B
  change S.ncard=A.ncard+B.ncard at number
  have left : S.ncard+4=widthAt F.n F.m F.r 6 := by omega
  have excess := (strict_single_six_stage_caps F paid six S global).2.2
  have live := (strict_six_complete_stage_shadow F paid six S global).2.2.2 (by omega)
  have Y := F.G.induce Sᶜ
  have exactRho : minimumExposure (F.G.induce Sᶜ) 5=4 := by omega
  have split := exposure_after_closed_stage_split F.G c.supp closed A B 5
  change minimumExposure (F.G.induce Sᶜ) 5=_ at split
  exact ⟨A,inside,by omega,global,left,exactRho,by omega⟩

theorem typed_width_of_original_rectangle {X:Type*} (G:SimpleGraph X) {s t r x y:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth G x y (originalThresholdCount n x+originalThresholdCount m y-1-r) := by
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  change ExactTypedWidth G x y (f+g-1-r)
  by_cases dead:f+g-1-r=0
  · exact Or.inl dead
  change 0<f at red
  change 0<g at blue
  let i := min r (f-1)
  let j := r-i
  have index : i+j=r := by dsimp [i,j];omega
  have a : i<f := by dsimp [i];omega
  have b : j<g := by dsimp [i,j];omega
  exact Or.inr ⟨f-i,g-j,by omega,by omega,by omega,uniform_rectangle_at G n m hn hm index a b row⟩

#print axioms single_six_stage_minimum_size
#print axioms last_six_residual_certificate
#print axioms typed_width_of_original_rectangle
end JSP452Audit.StarHost
