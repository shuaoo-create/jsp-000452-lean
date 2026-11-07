import ActualNineTwoEightGaps
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem nine_all_units_bound {s : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : NinePortRegion G)
    (n : Fin s→ℕ) (hn : Antitone n) (esc : K.totalCapacity<s)
    (rank : matchingEdges (G.induce K.chosen)=K.totalCapacity)
    (unit : originalThresholdCount ((componentBudget (G.induce K.chosen) n).entries n) 2=0) :
    let μ := K.totalCapacity
    let V := μ-originalThresholdCount n 2
    μ≤3*V+2 := by
  classical
  intro μ V
  let H := G.induce K.chosen
  let W := componentBudget H n
  have fit : W.loss≤μ := (component_budget_loss_le (G.induce K.chosen) n).trans_eq rank
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  obtain ⟨T,all⟩ := one_pattern_removes_all_nonunits n hn W live unit
  obtain ⟨_,slots⟩ := (mem_component_budget H n T.val).mp T.property
  obtain ⟨f,_⟩ := slots
  have size := Nat.card_le_card_of_injective f f.injective
  change Nat.card (Σz:↥T.val,Fin (n z.val+1))≤Nat.card ↥K.chosen at size
  rw [Nat.card_sigma] at size;simp only [Nat.card_fin,Nat.card_coe_set_eq] at size
  let big := (Finset.univ : Finset (Fin s)).filter (fun i => 2≤n i)
  have sub : big⊆T.val := fun i mem => all i (Finset.mem_filter.mp mem).2
  have charge : 3*originalThresholdCount n 2≤K.chosen.ncard := by
    calc
      _ = ∑_z∈big,3 := by simp [big,originalThresholdCount,Nat.mul_comm]
      _ ≤ ∑z∈big,(n z+1) := Finset.sum_le_sum (fun z hz => by have := (Finset.mem_filter.mp hz).2;omega)
      _ ≤ ∑z∈T.val,(n z+1) := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
      _ = ∑z:↥T.val,(n z.val+1) := Finset.sum_subtype T.val (fun _ => Iff.rfl) _
      _ ≤ _ := size
  have ord := K.chosen_structure.1
  change K.chosen.ncard=2*μ+2 at ord
  dsimp only [V];omega


theorem nine_raw_two_head_fee {s t : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : NinePortRegion G) (n : Fin s→ℕ) (m : Fin t→ℕ) (r j y : ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i)
    (esc : K.totalCapacity<s) (rank : matchingEdges (G.induce K.chosen)=K.totalCapacity)
    (active : 0<originalThresholdCount m j) (win : WinsHeight n m r j 2 y) (present : 0<widthAt n m r j)
    (few : originalThresholdCount n 2≤K.totalCapacity) :
    let μ := K.totalCapacity
    let W := componentBudget (G.induce K.chosen) n
    let δ := μ-W.loss
    let u := s-originalThresholdCount n 2
    let V := μ-originalThresholdCount n 2
    let v := originalThresholdCount (W.entries n) 2
    let C := K.basicPrice n m r j
    2*widthAt n m r j+2*(u+δ+originalThresholdCount m j)≤C+2*originalThresholdCount m y ∧
      (0<v → 2*widthAt n m r j+(V+v)+u+δ+originalThresholdCount m j≤C+originalThresholdCount m y) := by
  intro μ W δ u V v C
  let a := K.roots.ncard
  let J := commonErasedDemand n W a μ
  have fit : W.loss≤μ := (component_budget_loss_le (G.induce K.chosen) n).trans_eq rank
  change μ<s at esc
  change originalThresholdCount n 2≤μ at few
  have live : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have BL := original_threshold_one (W.entries n) (W.entries_positive n pn)
  have ZL := original_threshold_one J (common_erased_positive n W a μ)
  have br := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
    (a:=1) (b:=j) (h:=j) (by omega) (BL.symm ▸ live) active
  have zr := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a μ) hm
    (a:=1) (b:=j) (h:=j) (by omega) (ZL.symm ▸ live) active
  rw [BL] at br;rw [ZL] at zr
  have len : W.len+μ=s+δ := by change (s-W.loss)+μ=s+(μ-W.loss);omega
  have f := original_threshold_le_length n 2
  have eq := win.2.2.2.2.2
  have cost : C=a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j := rfl
  dsimp only [u,V]
  constructor
  · omega
  · intro yes
    have b2 := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm win.2.2.1 yes win.2.2.2.2.1
    change v+originalThresholdCount m y-1-(r+a)≤widthAt (W.entries n) m (r+a) j at b2
    omega


#print axioms nine_all_units_bound
#print axioms nine_raw_two_head_fee
end JSP452Audit.StarHost
