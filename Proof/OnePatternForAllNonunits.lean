import AllSubcapSingleTopBoundary
namespace JSP452Audit.StarHost
open SimpleGraph

/-- If the fixed exterior residual has no nonunit, a single feasible
pattern contains every original nonunit label. Use the first surviving
position of the individual pattern attaining the minimum. -/
theorem one_pattern_removes_all_nonunits {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n)
    (W : RemovalBudget s) (live : 0<W.len) (unit : originalThresholdCount (W.entries n) 2=0) :
    ∃T:↥W.choices,∀i,2≤n i → i∈T.val := by
  classical
  let i : Fin W.len := ⟨0,live⟩
  have small : W.entries n i<2 := by
    by_contra! larger
    have bad := (original_threshold_prefix (W.entries n) (W.entries_antitone n hn) 2 i).1 larger
    omega
  have member : W.entries n i∈W.choices.attach.image (fun T => n (W.label T i)) := Finset.min'_mem _ _
  obtain ⟨T,_,att⟩ := Finset.mem_image.mp member
  refine ⟨T,fun j high => ?_⟩
  by_contra keep
  have length := W.enough T
  have pos : 0<T.valᶜ.card := by omega
  have eq : W.label T i=T.valᶜ.orderEmbOfFin rfl ⟨0,pos⟩ := rfl
  rw [Finset.orderEmbOfFin_zero] at eq
  have first : W.label T i≤j := eq ▸ Finset.min'_le _ _ (Finset.mem_compl.mpr keep)
  have cost := hn first
  omega

theorem unit_residual_nonunit_volume {s D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (hn : Antitone n) (esc : matchingEdges (G.induce K.core)<s)
    (unit : originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2=0) :
    let μ := matchingEdges (G.induce K.core)
    let V := μ-originalThresholdCount n 2
    μ≤3*V+K.roots.ncard+minimumExposure G D := by
  classical
  intro μ V
  let H := G.induce K.core
  let W := componentBudget H n
  have fit : W.loss≤μ := component_budget_loss_le _ _
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  obtain ⟨T,all⟩ := one_pattern_removes_all_nonunits n hn W live unit
  obtain ⟨_,slots⟩ := (mem_component_budget H n T.val).mp T.property
  obtain ⟨f,_⟩ := slots
  have size := Nat.card_le_card_of_injective f f.injective
  change Nat.card (Σz:↥T.val,Fin (n z.val+1))≤Nat.card ↥K.core at size
  rw [Nat.card_sigma] at size;simp only [Nat.card_fin,Nat.card_coe_set_eq] at size
  let big := (Finset.univ : Finset (Fin s)).filter (fun i => 2≤n i)
  have sub : big⊆T.val := fun i mem => all i (Finset.mem_filter.mp mem).2
  have charge : 3*originalThresholdCount n 2≤K.core.ncard := by
    calc
      _ = ∑_z∈big,3 := by simp [big,originalThresholdCount,Nat.mul_comm]
      _ ≤ ∑z∈big,(n z+1) := Finset.sum_le_sum (fun z hz => by have := (Finset.mem_filter.mp hz).2;omega)
      _ ≤ ∑z∈T.val,(n z+1) := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
      _ = ∑z:↥T.val,(n z.val+1) := Finset.sum_subtype T.val (fun _ => Iff.rfl) _
      _ ≤ _ := size
  have ord := K.core_order
  change K.core.ncard=2*μ+K.roots.ncard+minimumExposure G D at ord
  dsimp only [V];omega

#print axioms one_pattern_removes_all_nonunits
#print axioms unit_residual_nonunit_volume
end JSP452Audit.StarHost
