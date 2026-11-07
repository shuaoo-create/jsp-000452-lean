import TwoStarsGeneral
open private JSP452Audit.StarHost.restrictStarCopy JSP452Audit.StarHost.component_of_star_vertex from ComponentStarLoad
namespace JSP452Audit.StarHost
open SimpleGraph

/-- If fewer than s vertices are marked, coloring all incident edges red
forces an entire positive blue forest on the unmarked original vertices. -/
theorem forced_blue_off_short_cover {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces G (forest n) (forest m)) (U : Set X) (short : U.ncard<s) :
    (forest m).IsContained (G.induce Uᶜ) := by
  let R : SimpleGraph X := {
    Adj a b := G.Adj a b ∧ (a∈U ∨ b∈U)
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  rcases force R (fun _ _ h => h.1) with red|blue
  · have many := forest_copy_matching R n pn red
    have few := matchingEdges_le_cover_card R U (fun _ _ h => h.2)
    rw [Fintype.card_fin] at many
    omega
  · obtain ⟨f⟩ := blue
    have outside (a : Vertices m) : f a∈Uᶜ := by
      obtain ⟨b,h⟩ := forest_has_neighbor m pm a
      have edge := f.toHom.map_rel h
      exact fun inside => edge.2 ⟨edge.1,Or.inl inside⟩
    let restricted : forest m →g G.induce Uᶜ :=
      ⟨fun a => ⟨f a,outside a⟩,fun h => (f.toHom.map_rel h).1⟩
    exact ⟨restricted.toCopy (fun _ _ eq => f.injective (congrArg Subtype.val eq))⟩

/-- A tight barrier of a forcing host cannot contain more than the
matching rank in excess of the blue length, provided one more vertex is
still too few for the red forest. -/
theorem forcing_tight_barrier_size {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces G (forest n) (forest m)) (short : matchingEdges G-t+1<s)
    (S : Set X) (tight : IsTightBarrier G S) : S.ncard≤matchingEdges G-t := by
  by_contra! large
  obtain ⟨U,sub,size⟩ := Set.exists_subset_card_eq (s:=S)
    (show matchingEdges G-t+1≤S.ncard by omega)
  have copy := forced_blue_off_short_cover G n m pn pm force U (by omega)
  have need := forest_copy_matching (G.induce Uᶜ) m pm copy
  rw [Fintype.card_fin] at need
  have account := tight_deletes_rank G S U tight sub
  omega

/-- In an odd factor-critical component the total number of disjoint
pairs counted within the *vertex sets* of the assigned stars is at most
the actual matching rank of the component. Edges between leaves are
unnecessary. Summing over the components preserves the same blue copy. -/
theorem critical_components_half_star_orders {X I : Type*} [Finite X] [Fintype I]
    (H : SimpleGraph X) (m : I→ℕ) (f : (forest m).Copy H)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    (∑i,(m i+1)/2)≤matchingEdges H := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  let owner (i : I) := H.connectedComponentMk (f (center m i))
  let A (c : H.ConnectedComponent) : Set I := {i | owner i=c}
  have per (c : H.ConnectedComponent) :
      (∑i:A c,(m i.val+1)/2)≤matchingEdges c.toSimpleGraph := by
    have inside (i : I) (hi : i∈A c) (j : Fin (m i+1)) : f ⟨i,j⟩∈c.supp :=
      (JSP452Audit.StarHost.component_of_star_vertex H m f i j).symm.trans hi
    let small := JSP452Audit.StarHost.restrictStarCopy H m f (A c) c.supp inside
    have space := Nat.card_le_card_of_injective small small.injective
    change Nat.card (Σi:A c, Fin (m i.val+1))≤Nat.card c.supp at space
    rw [Nat.card_sigma] at space
    simp only [Nat.card_fin] at space
    have pairs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : A c) _ =>
      show 2*((m i.val+1)/2)≤m i.val+1 by omega)
    rw [←Finset.mul_sum] at pairs
    have order := factorCritical_order_rank c.toSimpleGraph (crit c) c.nonempty_supp.to_subtype.some
    change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
    omega
  have all := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => per c)
  rw [←(component_rank_budget_gluing H).1] at all
  let ownerEquiv := Equiv.sigmaFiberEquiv owner
  have unpack := Fintype.sum_equiv ownerEquiv
    (fun p => (m p.2.val+1)/2) (fun i => (m i+1)/2) (fun _ => rfl)
  rw [Fintype.sum_sigma] at unpack
  exact unpack.symm.trans_le all

/-- The same critical tight barrier pays its cardinality and all half-star
orders. The excess weight includes every leaf after the first in pairs. -/
theorem forcing_critical_barrier_weight {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces G (forest n) (forest m)) (short : matchingEdges G-t+1<s)
    (S : Set X) (tight : IsTightBarrier G S)
    (crit : ∀c:(G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    S.ncard+t+(∑j,(m j-1)/2)≤matchingEdges G := by
  have bound := forcing_tight_barrier_size G n m pn pm force short S tight
  obtain ⟨f⟩ := forced_blue_off_short_cover G n m pn pm force S (by omega)
  have pairs := critical_components_half_star_orders (G.induce Sᶜ) m f crit
  have mass (j : Fin t) : (m j+1)/2=1+(m j-1)/2 := by have h:=pm j; omega
  simp_rw [mass] at pairs
  rw [Finset.sum_add_distrib] at pairs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_one] at pairs
  have loss := tight_deletes_rank G S S tight (Set.Subset.rfl)
  omega

/-- A strict minimum-edge host still has the two input forests, and the
same critical tight barrier pays the two weight bounds separately. -/
theorem failure_common_critical_barrier {s t : ℕ} (hs : 2≤s) (ht : 2≤t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑k∈Finset.Icc 2 (s+t),diagonal n m k) :
    ∃ (V : ℕ) (G : SimpleGraph (Fin V)) (S : Set (Fin V)),
      sizeRamsey (forest n) (forest m)=G.edgeSet.ncard ∧ Forces G (forest n) (forest m) ∧
      IsTightBarrier G S ∧
      (∀c:(G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) ∧
      matchingEdges G≤s+t-2 ∧
      S.ncard+t+(∑j,(m j-1)/2)≤matchingEdges G ∧
      S.ncard+s+(∑i,(n i-1)/2)≤matchingEdges G := by
  obtain ⟨V,G,edgeCount,force⟩ := star_min_attained n m
  have row := (finite_targets_row_zero G (by omega : 0<s) (by omega : 0<t) n m).mpr force
  have upper := erdos561_upper n m
  have strict : G.edgeSet.ncard<rowEnergy n m 0 := by rw [edgeCount,rowEnergy_zero]; omega
  have account := row_energy_budget (by omega) (by omega) n m hn hm pn pm G 0 row
  have count : rowCount s t 0=s+t-1 := by dsimp [rowCount]
  have rank : matchingEdges G≤s+t-2 := by omega
  obtain ⟨S,tight,parts⟩ := exists_critical_barrier G
  have crit (c:(G.induce Sᶜ).ConnectedComponent) := (parts c).2
  exact ⟨V,G,S,edgeCount.symm,force,tight,crit,rank,
    forcing_critical_barrier_weight G n m pn pm force (by omega) S tight crit,
    forcing_critical_barrier_weight G m n pm pn (forces_swap force) (by omega) S tight crit⟩

/-- Original antidiagonal equality in all lengths when paired extra leaves
on either side reach the other length less one. Both original lists are
unchanged, including each of their one-leaf entries. -/
theorem erdos561_of_paired_extra_leaves {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (enough : s-1≤∑j,(m j-1)/2 ∨ t-1≤∑i,(n i-1)/2) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (s+t),diagonal n m k := by
  by_cases small : min s t≤2
  · exact erdos561_smaller_length_at_most_two hs ht n m hn hm pn pm small
  by_contra fail
  obtain ⟨_,G,S,_,_,_,_,rank,blue,red⟩ :=
    failure_common_critical_barrier (by omega : 2≤s) (by omega : 2≤t) n m hn hm pn pm fail
  rcases enough with large|large <;> omega

/-- In particular a three-star failure can have only one free matching
edge beyond the blue length. Both the barrier and the entire long
profile draw on that same single unit. -/
theorem three_star_failure_residual {t : ℕ} (ht : 3≤t)
    (n : Fin 3→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑k∈Finset.Icc 2 (3+t),diagonal n m k) :
    ∃ (V : ℕ) (G : SimpleGraph (Fin V)) (S : Set (Fin V)),
      sizeRamsey (forest n) (forest m)=G.edgeSet.ncard ∧ Forces G (forest n) (forest m) ∧
      IsTightBarrier G S ∧
      (∀c:(G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) ∧
      t≤matchingEdges G ∧ matchingEdges G≤t+1 ∧ S.ncard+(∑j,(m j-1)/2)≤1 := by
  obtain ⟨V,G,S,size,force,tight,crit,rank,blue,_⟩ :=
    failure_common_critical_barrier (by decide : 2≤3) (by omega : 2≤t) n m hn hm pn pm fail
  exact ⟨V,G,S,size,force,tight,crit,by omega,by omega,by omega⟩

#print axioms forced_blue_off_short_cover
#print axioms forcing_tight_barrier_size
#print axioms critical_components_half_star_orders
#print axioms forcing_critical_barrier_weight
#print axioms failure_common_critical_barrier
#print axioms erdos561_of_paired_extra_leaves
#print axioms three_star_failure_residual
end JSP452Audit.StarHost


