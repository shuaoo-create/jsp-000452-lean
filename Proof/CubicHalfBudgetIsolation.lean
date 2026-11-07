import CubicTwoNeighborGrowth
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Delete exactly b labels in this graph and leave b/2 other actual
vertices isolated. All of their original neighbours are among the deletions. -/
theorem cubic_two_neighbor_deletion (H : SimpleGraph X) (cap : ∀v,Nat.card (H.neighborSet v)≤3)
    (low : ∀c:H.ConnectedComponent,∃v∈c.supp,Nat.card (H.neighborSet v)≤2)
    (μ b : ℕ) (short : b<μ) (order : 2*μ≤Nat.card X) :
    ∃I U:Set X,I.ncard=b/2 ∧ U.ncard=b ∧ U⊆Iᶜ ∧ ∀i∈I,∀v,H.Adj i v → v∈U := by
  obtain ⟨I,ind,size,used⟩ := cubic_independent_prefix H cap low (b/2) (by omega)
  have avoid : cubicOpen H I⊆Iᶜ := by
    rintro v ⟨i,hi,edge⟩ hv
    exact ind hi hv edge.ne edge
  have avail : b≤Iᶜ.ncard := by
    have tot := Set.ncard_add_ncard_compl I
    omega
  obtain ⟨U,all,away,uc⟩ := Set.exists_subsuperset_card_eq avoid (show (cubicOpen H I).ncard≤b by omega) avail
  exact ⟨I,U,size,uc,away,fun i hi v edge => all ⟨i,hi,edge⟩⟩

/-- Forest copies cannot use the isolated vertices. Odd criticality is
needed only to obtain a low-degree starting label in each intact component. -/
theorem cubic_robust_unused_labels {s : ℕ} (n : Fin s→ℕ) (pn : ∀i,1≤n i)
    (H : SimpleGraph X) {μ b : ℕ} (cap : ∀v,Nat.card (H.neighborSet v)≤3)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (short : b<μ) (order : 2*μ≤Nat.card X)
    (robust : ∀U:Set X,U.ncard≤b → (forest n).IsContained (H.induce Uᶜ)) :
    (∑i,n i)+s+b+b/2≤Nat.card X := by
  classical
  obtain ⟨I,U,ci,cu,apart,isolated⟩ := cubic_two_neighbor_deletion H cap
    (fun c => cubic_component_low_label H cap c (crit c)) μ b short order
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
  have size : S.ncard=b+b/2 := by dsimp [S];rw [Set.ncard_union_eq dis,cu,ci]
  have full := Set.ncard_add_ncard_compl S
  omega

/-- Sharpened mass of the actual cubic ordinary core. The numerator of
the floor is the original deletion budget, not a relaxed graph order. -/
theorem cubic_embedded_half_mass {s : ℕ} (G : SimpleGraph X) (K : DegreeRegion G 3)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (d : ℕ) (before : d<s)
    (cap : ∀v,Nat.card (G.neighborSet v)≤3) (inside : s≤matchingEdges (G.induce K.core)+d)
    (alt : WholeListRegionAlternative G K.core n d) :
    let μ := matchingEdges (G.induce K.core)
    (∑i,n i)+d+(μ+d-s)/2≤K.roots.ncard+μ+minimumExposure G 3 := by
  intro μ
  rcases alt with no|⟨_,_,robust⟩
  · change μ+d+1≤s at no;omega
  let b := μ+d-s
  have eqb : b+s=μ+d := by dsimp [b];change s≤μ+d at inside;omega
  have small : b<μ := by omega
  have total : Nat.card K.core=2*μ+K.roots.ncard+minimumExposure G 3 :=
    (Nat.card_coe_set_eq _).trans K.core_order
  have remain := cubic_robust_unused_labels n pn (G.induce K.core)
    (fun v => (induced_neighbor_count_le G K.core v).trans (cap _))
    (ordinary_core_components_critical G K) small (by omega : 2*μ≤Nat.card K.core)
    (robust_core_subtype n G K.core b robust)
  change (∑i,n i)+d+b/2≤K.roots.ncard+μ+minimumExposure G 3
  omega

#print axioms cubic_two_neighbor_deletion
#print axioms cubic_robust_unused_labels
#print axioms cubic_embedded_half_mass
end JSP452Audit.StarHost
