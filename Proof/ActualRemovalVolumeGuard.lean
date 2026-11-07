import StrictSubcapSingleNeedsUnitJoin
namespace JSP452Audit.StarHost
open SimpleGraph

theorem units_outside_high_prefix {s : ℕ} (n : Fin s→ℕ) :
    (Finset.univ.filter (fun z:Fin s => n z<2)).card=s-originalThresholdCount n 2 := by
  classical
  let high := Finset.univ.filter (fun z:Fin s => 2≤n z)
  have eq : Finset.univ.filter (fun z:Fin s => n z<2)=highᶜ := by
    ext z;simp [high]
  rw [eq,Finset.card_compl,Fintype.card_fin];rfl

/-- At maximum feasible removal, all vertex slots belong to the same
ordinary core. Each removed nonunit costs at least three slots, and
at most the number of original units can reduce this by one. -/
theorem removal_volume_guard {s D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) :
    let H := G.induce K.core
    let μ := matchingEdges H
    let W := componentBudget H n
    let u := s-originalThresholdCount n 2
    μ≤u+K.roots.ncard+minimumExposure G D+3*(μ-W.loss) := by
  classical
  intro H μ W u
  obtain ⟨T,mem,size⟩ := Finset.exists_mem_eq_sup W.choices W.present Finset.card
  change W.loss=T.card at size
  obtain ⟨bound,slots⟩ := (mem_component_budget H n T).mp mem
  obtain ⟨f,_⟩ := slots
  have place := Nat.card_le_card_of_injective f f.injective
  change Nat.card (Σz:↥T,Fin (n z.val+1))≤Nat.card ↥K.core at place
  rw [Nat.card_sigma] at place
  simp only [Nat.card_fin,Nat.card_coe_set_eq] at place
  have per (z:↥T) : 3≤n z.val+1+(if n z.val<2 then 1 else 0) := by have := pn z.val;split_ifs <;> omega
  have whole := Finset.sum_le_sum (s:=Finset.univ) (fun z _ => per z)
  let S := Finset.univ.filter (fun z:↥T => n z.val<2)
  let V := Finset.univ.filter (fun z:Fin s => n z<2)
  let send : ↥S → ↥V := fun z => ⟨z.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp z.property).2⟩⟩
  have inj : Function.Injective send := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun z:↥V => z.val) eq))
  have fewer : S.card≤V.card := by simpa using Fintype.card_le_of_injective send inj
  have orig : V.card=u := units_outside_high_prefix n
  have all : T.card*3≤(∑z:↥T,(n z.val+1))+S.card := by
    simpa [S,Finset.sum_add_distrib,Finset.sum_boole] using whole
  have ord := K.core_order
  change K.core.ncard=2*μ+K.roots.ncard+minimumExposure G D at ord
  change T.card≤μ at bound
  omega

/-- Common low-layer volume guard, retaining both copies of the
residual length gain. This applies independently of the color choice. -/
theorem twice_unit_volume {s D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (r d Y : ℕ)
    (fit : originalThresholdCount n 2≤matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s)
    (guard : K.roots.ncard+r+2*(d+Y)+(matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)
      ≤s-matchingEdges (G.induce K.core)) :
    let μ := matchingEdges (G.induce K.core)
    let δ := μ-(componentBudget (G.induce K.core) n).loss
    let u := s-originalThresholdCount n 2
    μ+r+2*d+2*Y≤2*u+2*δ+minimumExposure G D := by
  intro μ δ u
  have vol := removal_volume_guard G K n pn
  change μ≤u+K.roots.ncard+minimumExposure G D+3*δ at vol
  change originalThresholdCount n 2≤μ at fit
  change μ<s at esc
  change K.roots.ncard+r+2*(d+Y)+δ≤s-μ at guard
  dsimp only [u];dsimp only [u] at vol;omega

#print axioms removal_volume_guard
#print axioms twice_unit_volume
end JSP452Audit.StarHost
