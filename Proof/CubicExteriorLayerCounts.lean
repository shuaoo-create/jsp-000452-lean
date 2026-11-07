import OversizeBinaryExteriorRow
import CubicBinaryPeak
namespace JSP452Audit.StarHost

/-- Number of vertices in all stars of size at least two, retaining the
third leaf of every three-leaf star. -/
theorem cubic_nonunit_order {s : ℕ} (n : Fin s→ℕ) (cap : ∀i,n i≤3) :
    nonunitOrder n=3*originalThresholdCount n 2+originalThresholdCount n 3 := by
  classical
  let T := (Finset.univ : Finset (Fin s)).filter (fun i => 2≤n i)
  have restrict : (∑i∈T, (n i+1))=∑i:{i | 2≤n i}, (n i.val+1) :=
    Finset.sum_subtype T (fun i => by simp [T]) (fun i => n i+1)
  have all : nonunitOrder n=∑i:Fin s,if 2≤n i then n i+1 else 0 := by
    unfold nonunitOrder Vertices
    rw [Nat.card_sigma];simp only [Nat.card_fin]
    rw [←restrict,Finset.sum_filter]
  have point (i:Fin s) : (if 2≤n i then n i+1 else 0)=
      3*(if 2≤n i then 1 else 0)+(if 3≤n i then 1 else 0) := by
    have hi := cap i;split_ifs <;> omega
  rw [all];simp_rw [point];rw [Finset.sum_add_distrib,←Finset.mul_sum];simp [originalThresholdCount,Finset.sum_boole]

theorem threshold_tail_count {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n) (μ h : ℕ) :
    originalThresholdCount (remainingDemand n μ) h=originalThresholdCount n h-μ := by
  let A := originalThresholdCount n h
  let W := originalThresholdCount (remainingDemand n μ) h
  have sa : A≤s := original_threshold_le_length n h
  have sw : W≤s-μ := original_threshold_le_length _ h
  have each (i : Fin (s-μ)) : i.val<W ↔ μ+i.val<A := by
    have bound : μ+i.val<s := by have := i.isLt;omega
    let j : Fin s := ⟨μ+i.val,bound⟩
    have eq : remainingDemand n μ i=n j := dif_pos bound
    rw [←original_threshold_prefix (remainingDemand n μ) (remainingDemand_antitone n hn μ) h i,eq]
    exact original_threshold_prefix n hn h j
  change W=A-μ
  by_contra! ne
  rcases lt_or_gt_of_ne ne with below|above
  · let i : Fin (s-μ) := ⟨W,by omega⟩
    have iff := each i
    change W<W ↔ μ+W<A at iff;omega
  · let i : Fin (s-μ) := ⟨A-μ,by omega⟩
    have iff := each i
    change A-μ<W ↔ μ+(A-μ)<A at iff;omega

theorem row_area_three_layers {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (r : ℕ) :
    rowCount s t r+widthAt n m r 2+widthAt n m r 3≤rowEnergy n m r := by
  have point (z:ℕ) (mem:z∈Finset.range (rowCount s t r)) :
      1+(if 2≤diagonal n m (r+z+2) then 1 else 0)+(if 3≤diagonal n m (r+z+2) then 1 else 0)≤
      diagonal n m (r+z+2) := by
    have inR := Finset.mem_range.mp mem
    obtain ⟨i,j,_,peak⟩ := diagonal_attained n m hs ht (r+z) (by dsimp [rowCount] at inR;omega)
    have := pn i;have := pm j;split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.range (rowCount s t r)) point
  simpa [rowEnergy,widthAt,offsetsAt,Finset.sum_add_distrib,Finset.sum_boole] using sum

/-- When positive, the two exterior thresholds supply genuine rectangles.
The height-two blue rectangle also applies to an all-unit red exterior list. -/
theorem exterior_binary_layer_bounds {S t : ℕ} (hS : 0<S) (ht : 0<t) (n : Fin S→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (r : ℕ)
    (blue : 0<originalThresholdCount m 2) :
    let A := originalThresholdCount n 2
    let B := originalThresholdCount m 2
    S+B-1-r≤widthAt n m r 2 ∧
      (0<A → A+t-1-r≤widthAt n m r 2 ∧ A+B-1-r≤widthAt n m r 3) := by
  intro A B
  have one := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=2) (h:=2) (by decide)
    (by rw [original_threshold_one n pn];exact hS) blue
  rw [original_threshold_one n pn] at one
  refine ⟨one,?_⟩
  intro pos
  have red := actual_rectangle_le_column (r:=r) n m hn hm (a:=2) (b:=1) (h:=2) (by decide) pos
    (by rw [original_threshold_one m pm];exact ht)
  rw [original_threshold_one m pm] at red
  exact ⟨red,actual_rectangle_le_column n m hn hm (a:=2) (b:=2) (h:=3) (by decide) pos blue⟩

#print axioms cubic_nonunit_order
#print axioms threshold_tail_count
#print axioms row_area_three_layers
#print axioms exterior_binary_layer_bounds
end JSP452Audit.StarHost
