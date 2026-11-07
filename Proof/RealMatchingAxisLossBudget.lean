import ActualEvenCutAxisInventory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The even cut applies whenever enough red stars remain. Below that
trigger the unassisted nonnegative inventories already give the same fee. -/
theorem matching_axis_double_loss (f t r a μ Y w v b z : ℕ)
    (space : t+2*Y≤μ) (tpos : 0<t) (choose : w=μ+1-(t+Y)) (live : 0<v)
    (extra : 2*w<f → f-2*w+v-1-(r+a)≤b ∧ f-2*w+v-1-r≤z) :
    2*(f+t-1-r)-(a+2*μ+b+z)≤f := by
  let q := μ-(t+2*Y)+1
  let L := 2*(f+t-1-r)-(a+2*μ+b+z)
  have cheap : L≤2*(f-q) := by dsimp [L,q];omega
  have flat : L≤2*q := by
    by_cases many : 2*w<f
    · obtain ⟨left,right⟩ := extra many
      dsimp [L,q];omega
    · dsimp [L,q];omega
  change L≤f
  omega

noncomputable def doubleEnvelopeLoss {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (r h : ℕ) : ℕ :=
  2*widthAt n m r h-(K.roots.ncard+2*matchingEdges (G.induce K.core)+
    uniformEnvelope (G.induce K.rest) h+uniformEnvelope (eraseInternal G K.core) h)

theorem actual_matching_axis_loss {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (space : t+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)) (h : ℕ) (pos : 0<h)
    (winner : WinsHeight n m r h h 1) : doubleEnvelopeLoss G K n m r h≤originalThresholdCount n h := by
  let μ := matchingEdges (G.induce K.core)
  let Y := ∑j,(m j-1)/2
  let w := μ+1-(t+Y)
  let V := halfOrderBudget m (μ-w)
  obtain ⟨live,all⟩ := exact_axis_repair_inventory G K n m hn hm pn pm ht row (by change t+Y≤μ;change t+2*Y≤μ at space;omega)
  have eq := winner.2.2.2.2.2
  rw [original_threshold_one m pm] at eq
  unfold doubleEnvelopeLoss
  rw [eq]
  exact matching_axis_double_loss _ t r K.roots.ncard μ Y w V.len _ _ space ht rfl live (all h pos)

/-- Each original star contributes at most twice its half-order extra
to the full sum of its thresholds from three up. -/
theorem large_threshold_sum {s : ℕ} (n : Fin s→ℕ) (D : ℕ) :
    (∑j∈Finset.range D,originalThresholdCount n (j+3))≤2*∑i,(n i-1)/2 := by
  classical
  have single (i:Fin s) : (∑j∈Finset.range D,if j+3≤n i then 1 else 0)≤2*((n i-1)/2) := by
    rw [Finset.sum_boole]
    have sub : (Finset.range D).filter (fun j => j+3≤n i) ⊆ Finset.range (2*((n i-1)/2)) := by
      intro j hj
      have := (Finset.mem_filter.mp hj).2
      apply Finset.mem_range.mpr;omega
    simpa using Finset.card_le_card sub
  have bound := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => single i)
  rw [Finset.sum_comm,←Finset.mul_sum] at bound
  simpa [originalThresholdCount,Finset.sum_boole] using bound

noncomputable def matchingAxesFromThree {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r D : ℕ) : Finset ℕ := by
  classical exact (Finset.range (D-2)).filter (fun z => WinsHeight n m r (z+3) (z+3) 1)

theorem sum_actual_matching_axes {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (space : t+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)) :
    let axes := matchingAxesFromThree n m r D
    (∑z∈axes,doubleEnvelopeLoss G K n m r (z+3))≤2*∑i,(n i-1)/2 := by
  classical
  intro axes
  have point (z:ℕ) (mem:z∈axes) :=
    actual_matching_axis_loss G K n m ht hn hm pn pm row space (z+3) (by omega)
      (by change z∈(Finset.range (D-2)).filter (fun z => WinsHeight n m r (z+3) (z+3) 1) at mem
          exact (Finset.mem_filter.mp mem).2)
  have part := Finset.sum_le_sum (s:=axes) point
  have sub : axes⊆Finset.range (D-2) := Finset.filter_subset _ _
  exact part.trans ((Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)).trans
    (large_threshold_sum n (D-2)))

#print axioms matching_axis_double_loss
#print axioms actual_matching_axis_loss
#print axioms large_threshold_sum
#print axioms sum_actual_matching_axes
end JSP452Audit.StarHost
