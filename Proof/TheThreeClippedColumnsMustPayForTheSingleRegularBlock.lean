import ProjectTheActualTwoStageExposureBoundsBackToTheWinningRegularColumns
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_third_three_columns (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let W := widthAt F.n F.m F.r
    let O := B.outside
    let P := B.P
    let i := P-(F.r+1)
    let g := (O.induce (peakPrefix O i)ᶜ).edgeSet.ncard-rowEnergy F.n F.m (F.r+i+P)
    g+3*P+p+min i (peakCountAbove O H)+min i (peakCountAbove O (H+1))+min i (peakCountAbove O (H+2))≤
      min (i+P) (W (H+1))+min (i+P) (W (H+2))+min (i+P) (W (H+3)) := by
  intro H W O P i g
  let D := 2*p
  let U := peakPrefix O i
  let Y := O.induce Uᶜ
  let E := rowEnergy F.n F.m (F.r+i+P)
  obtain ⟨_,inv,_,_,_,_,bill⟩ := regular_block_inventory_and_next F paid B degree head one
  change E≤Y.edgeSet.ncard at bill
  have gain : Y.edgeSet.ncard=E+g := by change Y.edgeSet.ncard=E+(Y.edgeSet.ncard-E);omega
  have cap (v:↥(B.piece.suppᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤D :=
    (induced_neighbor_count_le F.G _ v).trans (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq degree)
  have edges := B.original_geometry.2.2.2.1
  change F.G.edgeSet.ncard=O.edgeSet.ncard+D*P+p at edges
  have spent := peak_prefix_layer_price O D i cap
  change O.edgeSet.ncard=Y.edgeSet.ncard+_ at spent
  have strict := F.strict
  have height : diagonal F.n F.m (F.r+2)=D+1 := by dsimp only [D];have many := strict_source_degree_at_least_eleven F paid;omega
  have eq := profile_shift_exact_loss F.hs F.ht F.n F.m F.hn F.hm (show F.r≤F.r from le_rfl) height.le (i+P)
  rw [Finset.sum_range_succ,←Nat.add_assoc F.r i P] at eq
  have peak := width_at_peak F.hs F.ht F.n F.m F.hn F.hm F.r
  rw [height,one] at peak
  change W (D+1)=1 at peak
  change rowEnergy F.n F.m F.r=E+((∑j∈Finset.range D,min (i+P) (W (j+1)))+min (i+P) (W (D+1))) at eq
  rw [peak] at eq
  change H+3=D at head
  rw [←head,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ] at spent
  rw [←head,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ] at eq
  have deposited : (∑j∈Finset.range H,min i (peakCountAbove O j))=H*i := by
    calc
      _ = ∑_j∈Finset.range H,i := Finset.sum_congr rfl (fun j hj => min_eq_left
        ((Nat.sub_le P (F.r+1)).trans (inv.le.trans (peak_counts_antitone O (by have := Finset.mem_range.mp hj;omega)))))
      _ = _ := by simp
  have upper : (∑j∈Finset.range H,min (i+P) (W (j+1)))≤H*(i+P) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.range H) (fun j _ => Nat.min_le_left (i+P) (W (j+1)))
  rw [deposited] at spent
  have mult : D*P=H*P+3*P := by rw [←head,Nat.add_mul]
  rw [Nat.mul_add] at upper
  change rowEnergy F.n F.m F.r=E+(((((∑j∈Finset.range H,min (i+P) (W (j+1)))+min (i+P) (W (H+1)))+min (i+P) (W (H+2)))+min (i+P) (W (H+3)))+min (i+P) 1) at eq
  omega

#print axioms regular_third_three_columns
end JSP452Audit.StarHost
