import ActualIsolatedLabels
import StrictSourceWholeListConstraints
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A positive forest in the surviving graph cannot use any of the isolated
labels. Count the copied vertices before identifying the unused budget. -/
theorem robust_unused_labels_bound {s : ℕ} (n : Fin s→ℕ) (pn : ∀i,1≤n i)
    (H : SimpleGraph X) {D μ b : ℕ} (pos : 0<D) (cap : ∀v,Nat.card (H.neighborSet v)≤D)
    (short : b<μ) (order : 2*μ≤Nat.card X)
    (robust : ∀U:Set X,U.ncard≤b → (forest n).IsContained (H.induce Uᶜ)) :
    (∑i,n i)+s+b+b/D≤Nat.card X := by
  classical
  obtain ⟨I,U,ci,cu,apart,isolated⟩ := deletion_isolates_labels H pos cap short order
  obtain ⟨f⟩ := robust U cu.le
  let S := U∪I
  let send (v:Vertices n) : ↥Sᶜ := ⟨(f v).val,by
    obtain ⟨w,e⟩ := forest_has_neighbor n pn v
    have edge : H.Adj (f v).val (f w).val := f.toHom.map_adj e
    have free : (f v).val∉I := fun h => (f w).property (isolated _ h _ edge)
    exact fun h => h.elim (f v).property free⟩
  have bound := Nat.card_le_card_of_injective send (fun a b eq => f.injective (Subtype.ext
    (congrArg (fun y : ↥Sᶜ => y.val) eq)))
  change Nat.card (Σi:Fin s,Fin (n i+1))≤Nat.card ↥Sᶜ at bound
  rw [Nat.card_sigma,Nat.card_coe_set_eq] at bound
  simp only [Nat.card_fin,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at bound
  have vertices : (∑i,n i)+s≤Sᶜ.ncard := by simpa using bound
  have dis : Disjoint U I := Set.disjoint_left.mpr (fun _ hu hi => apart hu hi)
  have size : S.ncard=b+b/D := by dsimp [S];rw [Set.ncard_union_eq dis,cu,ci]
  have full := Set.ncard_add_ncard_compl S
  omega

/-- On the actual ordinary region the unused-label bound gains floor(b/D)
edges over the crude whole-forest mass bound. -/
theorem embedded_list_unused_mass {s D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (d : ℕ) (before : d<s)
    (pos : 0<D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (inside : s≤matchingEdges (G.induce K.core)+d)
    (alt : WholeListRegionAlternative G K.core n d) :
    let μ := matchingEdges (G.induce K.core)
    (∑i,n i)+d+(μ+d-s)/D≤K.roots.ncard+μ+minimumExposure G D := by
  intro μ
  rcases alt with no|⟨_,_,robust⟩
  · change μ+d+1≤s at no;omega
  let b := μ+d-s
  have eqb : b+s=μ+d := by dsimp [b];change s≤μ+d at inside;omega
  have small : b<μ := by omega
  have total : Nat.card K.core=2*μ+K.roots.ncard+minimumExposure G D :=
    (Nat.card_coe_set_eq _).trans K.core_order
  have remain := robust_unused_labels_bound n pn (G.induce K.core) pos
    (fun v => (induced_neighbor_count_le G K.core v).trans (cap _)) small
    (by omega : 2*μ≤Nat.card K.core) (robust_core_subtype n G K.core b robust)
  change (∑i,n i)+d+b/D≤K.roots.ncard+μ+minimumExposure G D
  omega

#print axioms robust_unused_labels_bound
#print axioms embedded_list_unused_mass
end JSP452Audit.StarHost
