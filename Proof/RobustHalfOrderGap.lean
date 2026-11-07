import EvenDeletionInCriticalPieces
import RobustRegionForests
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

theorem robust_core_subtype {s : ℕ} (n : Fin s→ℕ) (G : SimpleGraph X) (A : Set X) (b : ℕ)
    (actual : ∀W:Set X,W⊆A → W.ncard≤b → (forest n).IsContained (G.induce (A\W))) :
    ∀U:Set A,U.ncard≤b → (forest n).IsContained ((G.induce A).induce Uᶜ) := by
  intro U size
  let W := Subtype.val '' U
  have sub : W⊆A := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have count : W.ncard=U.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  obtain ⟨f⟩ := actual W sub (count.symm ▸ size)
  let v (z : Vertices n) : A := ⟨(f z).val,(f z).property.1⟩
  have retained (z : Vertices n) : v z∉U := fun h => (f z).property.2 ⟨v z,h,rfl⟩
  let send (z : Vertices n) : ↥(Uᶜ : Set A) := ⟨v z,retained z⟩
  refine ⟨{toHom := {toFun := send,map_rel' := fun e => f.toHom.map_adj e},injective' := ?_}⟩
  intro z w eq
  exact f.injective (Subtype.ext (congrArg (fun t : ↥(Uᶜ : Set A) => t.val.val) eq))

theorem ordinary_core_components_critical (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D)
    (c : (G.induce K.core).ConnectedComponent) : PerfectAfterEveryDeletion c.toSimpleGraph := by
  let e := coreComponentIso G K.barrier K.pieces c
  exact perfect_after_deletion_of_iso e.symm (K.critical _).2

/-- The deletion budget is μ+d−s in natural arithmetic with s≤μ+d.
The half-order charge gives s+d+2·Σ floor((nᵢ−1)/2)≤μ+1. -/
theorem robust_whole_half_order {s : ℕ} (H : SimpleGraph X) (n : Fin s→ℕ) (pn : ∀i,1≤n i)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (d : ℕ) (smallD : d≤s) (trigger : s≤matchingEdges H+d)
    (robust : ∀U:Set X,U.ncard≤matchingEdges H+d-s → (forest n).IsContained (H.induce Uᶜ)) :
    s+d+2*(∑i,(n i-1)/2)≤matchingEdges H+1 := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  let b := matchingEdges H+d-s
  have bsize : b+s=matchingEdges H+d := by dsimp [b];omega
  have room : b/2≤matchingEdges H := by omega
  obtain ⟨U,card,charge⟩ := region_even_deletion_set H crit (b/2) room
  obtain ⟨f⟩ := robust U (show U.ncard≤b by omega)
  have bound := critical_half_orders_off_cover H n U f crit
  rw [charge] at bound
  have mass (i:Fin s) : (n i+1)/2=1+(n i-1)/2 := by have hi:=pn i;omega
  simp_rw [mass] at bound
  rw [Finset.sum_add_distrib] at bound
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at bound
  have numeric : s+(∑i,(n i-1)/2)+b/2≤matchingEdges H := by simpa using bound
  have twice := Nat.mul_le_mul_left 2 numeric
  have split : b≤2*(b/2)+1 := by omega
  omega

theorem strict_source_whole_list_gap (F : StrictFamily.{u}) {D : ℕ} (K : DegreeRegion F.G D) :
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    (μ+d+1≤F.s ∨ F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1) ∧
    (μ+d+1≤F.t ∨ F.t+d+2*(∑i,(F.m i-1)/2)≤μ+1) := by
  intro μ d
  obtain ⟨red,blue⟩ := strict_source_robust_whole_forests F K
  have lengths := (strict_source_strong_lengths F).1
  change F.r+d+1≤min F.s F.t at lengths
  obtain ⟨ls,lt⟩ := le_min_iff.mp lengths
  constructor
  · by_cases active : F.s≤μ+d
    · exact Or.inr (robust_whole_half_order (F.G.induce K.core) F.n F.pn
        (ordinary_core_components_critical F.G K) d (by omega) active
        (robust_core_subtype F.n F.G K.core _ (red active)))
    · exact Or.inl (by omega)
  · by_cases active : F.t≤μ+d
    · exact Or.inr (robust_whole_half_order (F.G.induce K.core) F.m F.pm
        (ordinary_core_components_critical F.G K) d (by omega) active
        (robust_core_subtype F.m F.G K.core _ (blue active)))
    · exact Or.inl (by omega)

#print axioms robust_core_subtype
#print axioms ordinary_core_components_critical
#print axioms robust_whole_half_order
#print axioms strict_source_whole_list_gap
end JSP452Audit.StarHost
