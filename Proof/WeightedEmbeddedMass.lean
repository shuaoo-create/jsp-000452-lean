import RobustUnusedMass
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Weighted whole-forest mass on the actual core, with the explicit
remainder of the integer division bounded by D-1. -/
theorem embedded_robust_mass_weighted {s D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (d : ℕ) (before : d<s)
    (pos : 0<D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (inside : s≤matchingEdges (G.induce K.core)+d) (alt : WholeListRegionAlternative G K.core n d) :
    let μ := matchingEdges (G.induce K.core)
    D*(∑i,n i)+(D+1)*d+1 ≤ (D-1)*μ+s+D*(K.roots.ncard+minimumExposure G D)+D := by
  intro μ
  let b := μ+d-s
  have eqb : b+s=μ+d := by change s≤μ+d at inside;dsimp [b];omega
  have mass := embedded_list_unused_mass G K n pn d before pos cap inside alt
  change (∑i,n i)+d+b/D≤K.roots.ncard+μ+minimumExposure G D at mass
  have scaled := Nat.mul_le_mul_left D mass
  simp only [Nat.mul_add] at scaled ⊢
  have mod := Nat.mod_add_div b D
  have rem := Nat.mod_lt b pos
  have base : D*μ=(D-1)*μ+μ := by
    conv_lhs => rw [show D=D-1+1 by omega]
    rw [Nat.add_mul,Nat.one_mul]
  rw [Nat.add_mul,Nat.one_mul]
  omega

/-- A full head forces at least one positive unused label in the robust
mass bound, since the protected half-order already pays its leaves. -/
theorem embedded_full_head_unused_one {s D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (d : ℕ) (two : 2≤d) (before : d<s)
    (pos : 0<D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (i : Fin s) (head : n i=D)
    (inside : s≤matchingEdges (G.induce K.core)+d) (alt : WholeListRegionAlternative G K.core n d) :
    (∑j,n j)+d+1≤K.roots.ncard+matchingEdges (G.induce K.core)+minimumExposure G D := by
  let μ := matchingEdges (G.induce K.core)
  have mass := embedded_list_unused_mass G K n pn d before pos cap inside alt
  obtain ⟨half,_,_⟩ := alt.resolve_left (by change ¬(μ+d+1≤s);change s≤μ+d at inside;omega)
  have entry : (n i-1)/2≤∑j,(n j-1)/2 :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((n j-1)/2)) (Finset.mem_univ i)
  rw [head] at entry
  change s+d+2*(∑j,(n j-1)/2)≤μ+1 at half
  have fit : D≤μ+d-s := by omega
  have one : 1≤(μ+d-s)/D := (Nat.le_div_iff_mul_le pos).mpr (by simpa using fit)
  change (∑j,n j)+d+(μ+d-s)/D≤K.roots.ncard+μ+minimumExposure G D at mass
  change (∑j,n j)+d+1≤K.roots.ncard+μ+minimumExposure G D
  omega

#print axioms embedded_robust_mass_weighted
#print axioms embedded_full_head_unused_one
end JSP452Audit.StarHost
