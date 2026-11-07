import ConservativeBudgetOnActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_seven_whole_menu_prices {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (eight:diagonal F.n F.m (F.r+2)-1=8)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8)
    (k:ℕ) (menu:SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+k))
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 8 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 7 C)
    (fit:k≤B.ncard+C.ncard) :
    let P := ∑i,Nat.card (e i).supp/2
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 8
    P+4*Fintype.card I+1+min k B.ncard≤L+h ∧
      4*Fintype.card I+1+min k B.ncard≤k+h := by
  intro P h L
  let O := F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ
  obtain ⟨V,num,save⟩ := two_stage_exact_prefix O 7 B first C second k fit
  have priced := actual_eight_conservative_baseline F paid e actual V (by rw [num];exact menu)
  change rowEnergy F.n F.m (F.r+V.ncard+P)≤(O.induce Vᶜ).edgeSet.ncard ∧
    F.G.edgeSet.ncard=O.edgeSet.ncard+8*P+4*Fintype.card I at priced
  rw [num] at priced
  have top : diagonal F.n F.m (F.r+2)=9 := by omega
  have old := (minimal_rank_exact_source F paid).2.1
  have seven := prefix_at_two_top_columns F.hs F.ht F.n F.m F.hn F.hm 7 top (k+P)
  have eightTax := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r (k+P) 8 top.le
  rw [show 8+1=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at eightTax
  rw [←Nat.add_assoc] at seven eightTax
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k+P)+7*(k+P)+L+h at seven
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k+P)+8*(k+P)+h at eightTax
  clear * - old seven eightTax priced save
  constructor <;> omega

theorem regular_eight_menu_must_pass_seven {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (eight:diagonal F.n F.m (F.r+2)-1=8)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8)
    (k:ℕ) (menu:SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+k))
    (cases:(Fintype.card I=1 ∧ highestWidth F.n F.m F.r=1) ∨ (Fintype.card I=2 ∧ highestWidth F.n F.m F.r≤4))
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 8 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 7 C) :
    B.ncard+C.ncard<k := by
  by_contra! fit
  have price := eight_seven_whole_menu_prices F paid eight e actual k menu B first C second fit
  have elements (c) (hc:c∈Finset.univ.map e) : c∈oddRegularComponents F.G 8 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hc;exact actual i
  have shadow := strict_eight_exterior_stage_bound F paid eight (Finset.univ.map e) elements B first
  rw [Finset.sum_map,Finset.card_map,Finset.card_univ] at shadow
  change widthAt F.n F.m F.r 8+Fintype.card I≤(∑i,Nat.card (e i).supp/2)+B.ncard+(22+2*highestWidth F.n F.m F.r)/5 at shadow
  by_cases high:k≤B.ncard
  · rw [min_eq_left high] at price;omega
  · rw [min_eq_right (by omega : B.ncard≤k)] at price;omega

#print axioms eight_seven_whole_menu_prices
#print axioms regular_eight_menu_must_pass_seven
end JSP452Audit.StarHost
