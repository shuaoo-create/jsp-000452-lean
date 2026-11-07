import AConservativeTenDegreeMenuOnTheActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_nine_whole_menu_prices {I:Type*} [Fintype I] [DecidableEq I] 
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (K:TenRegularBudget F.G) (e:I↪F.G.ConnectedComponent) (sel:Finset.univ.map e=K.selected)
    (z:I→ℕ) (ranks:∀i,matchingEdges (e i).toSimpleGraph≤z i) (budget:(∑i,z i)=K.P)
    (k:ℕ) (menu:SplitCapacities z (F.r+k))
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 10 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 9 C)
    (fit:k≤B.ncard+C.ncard) :
    let P := K.P
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 10
    P+5*K.eps+1+min k B.ncard≤L+h ∧
      5*K.eps+1+min k B.ncard≤k+h := by
  intro P h L
  let O := F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ
  obtain ⟨V,num,save⟩ := two_stage_exact_prefix O 9 B first C second k fit
  have priced := actual_ten_conservative_baseline F paid K e sel z ranks budget V (by rw [num];exact menu)
  change rowEnergy F.n F.m (F.r+V.ncard+P)≤(O.induce Vᶜ).edgeSet.ncard ∧
    F.G.edgeSet.ncard=O.edgeSet.ncard+10*P+5*K.eps at priced
  rw [num] at priced
  have top : diagonal F.n F.m (F.r+2)=11 := by omega
  have old := (minimal_rank_exact_source F paid).2.1
  have seven := prefix_at_two_top_columns F.hs F.ht F.n F.m F.hn F.hm 9 top (k+P)
  have eightTax := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r (k+P) 10 top.le
  rw [show 10+1=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at eightTax
  rw [←Nat.add_assoc] at seven eightTax
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k+P)+9*(k+P)+L+h at seven
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k+P)+10*(k+P)+h at eightTax
  clear * - old seven eightTax priced save
  constructor <;> omega


theorem ten_closed_stage_width (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G)
    (I:Set ↥K.support) (inner:CompleteDegreeStage (F.G.induce K.support) 10 I)
    (B:Set ↥(K.supportᶜ:Set F.X)) (first:CompleteDegreeStage (F.G.induce K.supportᶜ) 10 B) :
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 10
    I.ncard≤matchingEdges (F.G.induce K.support) ∧ L≤I.ncard+B.ncard+(38+2*h)/7 := by
  intro h L
  have reg (x:↥K.support) : Nat.card ((F.G.induce K.support).neighborSet x)=10 :=
    (closed_set_degree_eq F.G K.support K.support_closed x).trans (K.support_full x.val x.property)
  have capI := full_independent_set_le_matching (F.G.induce K.support) 10 (by decide)
    (fun x => (reg x).le) I inner.1 inner.2.1
  obtain ⟨both,num⟩ := join_closed_degree_stages F.G K.support 10 K.support_closed I B inner first
  obtain ⟨_,_,_,_,lower,upper⟩ := strict_ten_complete_stage F paid ten _ both
  change L-_≤_ at lower
  change 7*_≤38+2*h at upper
  exact ⟨capI,by omega⟩

#print axioms ten_nine_whole_menu_prices
#print axioms ten_closed_stage_width
end JSP452Audit.StarHost
