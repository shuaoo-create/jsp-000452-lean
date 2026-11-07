import ThreeStarBarrier
open private JSP452Audit.StarHost.restrictStarCopy JSP452Audit.StarHost.component_of_star_vertex from ComponentStarLoad
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Vertices forbidden to a blue copy consume one unit of the component's
rank per pair of forbidden labels in that component. The estimate counts
actual vertices, so no adjacency of a forbidden pair is required. -/
theorem critical_half_orders_off_cover {X I : Type*} [Finite X] [Fintype I]
    (H : SimpleGraph X) [Fintype H.ConnectedComponent] (m : I→ℕ) (U : Set X)
    (f : (forest m).Copy (H.induce Uᶜ))
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    (∑i,(m i+1)/2)+(∑c:H.ConnectedComponent,(c.supp∩U).ncard/2)≤matchingEdges H := by
  classical
  let g := (Embedding.induce (G:=H) Uᶜ).toCopy.comp f
  let owner (i : I) := H.connectedComponentMk (g (center m i))
  let A (c : H.ConnectedComponent) : Set I := {i | owner i=c}
  have per (c : H.ConnectedComponent) :
      (∑i:A c,(m i.val+1)/2)+(c.supp∩U).ncard/2≤matchingEdges c.toSimpleGraph := by
    have inside (i : I) (hi : i∈A c) (j : Fin (m i+1)) : g ⟨i,j⟩∈c.supp\U :=
      ⟨(JSP452Audit.StarHost.component_of_star_vertex H m g i j).symm.trans hi,(f ⟨i,j⟩).property⟩
    let small := JSP452Audit.StarHost.restrictStarCopy H m g (A c) (c.supp\U) inside
    have space := Nat.card_le_card_of_injective small small.injective
    change Nat.card (Σi:A c,Fin (m i.val+1))≤Nat.card (c.supp\U : Set X) at space
    rw [Nat.card_sigma,Nat.card_coe_set_eq] at space
    simp only [Nat.card_fin] at space
    have pairs := Finset.sum_le_sum (s:=Finset.univ) (fun (i : A c) _ =>
      show 2*((m i.val+1)/2)≤m i.val+1 by omega)
    rw [←Finset.mul_sum] at pairs
    have split := Set.ncard_sdiff_add_ncard c.supp (c.supp∩U)
    rw [Set.sdiff_self_inter,Set.union_eq_self_of_subset_right Set.inter_subset_left] at split
    have order := factorCritical_order_rank c.toSimpleGraph (crit c) c.nonempty_supp.to_subtype.some
    change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
    rw [Nat.card_coe_set_eq] at order
    omega
  have all := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => per c)
  rw [Finset.sum_add_distrib,←(component_rank_budget_gluing H).1] at all
  let ownerEquiv := Equiv.sigmaFiberEquiv owner
  have unpack := Fintype.sum_equiv ownerEquiv
    (fun p => (m p.2.val+1)/2) (fun i => (m i+1)/2) (fun _ => rfl)
  rw [Fintype.sum_sigma] at unpack
  rwa [←unpack]

/-- With three red stars, there are two labels available to color as red
centers. Choosing them in one positive-rank component reduces the blue
pair capacity by a full unit. -/
theorem three_star_critical_pair_charge {X : Type*} [Finite X] (H : SimpleGraph X)
    {t : ℕ} (n : Fin 3→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (force : Forces H (forest n) (forest m)) (positive : 0<matchingEdges H)
    (crit : ∀c:H.ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    t+(∑j,(m j-1)/2)+1≤matchingEdges H := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  have total := (component_rank_budget_gluing H).1
  rw [total,Finset.sum_pos_iff] at positive
  obtain ⟨c,_,pos⟩ := positive
  have order := factorCritical_order_rank c.toSimpleGraph (crit c) c.nonempty_supp.to_subtype.some
  change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at order
  rw [Nat.card_coe_set_eq] at order
  obtain ⟨U,inside,size⟩ := Set.exists_subset_card_eq (s:=c.supp) (show 2≤c.supp.ncard by omega)
  obtain ⟨f⟩ := forced_blue_off_short_cover H n m pn pm force U (by omega)
  have price := critical_half_orders_off_cover H m U f crit
  have one := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun z:H.ConnectedComponent => (z.supp∩U).ncard/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  rw [Set.inter_eq_right.mpr inside,size] at one
  have mass (j : Fin t) : (m j+1)/2=1+(m j-1)/2 := by have h:=pm j; omega
  simp_rw [mass] at price
  rw [Finset.sum_add_distrib] at price
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_one] at price
  omega

/-- Three arbitrary positive stars against any positive forest with at
least one star having three or more leaves. The lists are the original
lists used in the size Ramsey number. -/
theorem erdos561_three_against_nonbinary {t : ℕ} (ht : 0<t)
    (n : Fin 3→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (big : ∃j,3≤m j) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (3+t),diagonal n m k := by
  by_cases small : t≤2
  · exact erdos561_smaller_length_at_most_two (by decide) ht n m hn hm pn pm (by omega)
  by_contra fail
  obtain ⟨V,G,S,_,force,_,crit,floorG,rank,account⟩ :=
    three_star_failure_residual (by omega : 3≤t) n m hn hm pn pm fail
  obtain ⟨j,heavy⟩ := big
  have term := Finset.single_le_sum (s:=Finset.univ) (f:=fun i:Fin t => (m i-1)/2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have weight : 1≤∑i:Fin t,(m i-1)/2 := by omega
  have empty := (Set.ncard_eq_zero (s:=S)).mp (show S.ncard=0 by omega)
  subst S
  rw [show ((∅ : Set (Fin V))ᶜ)=Set.univ by ext; simp] at crit
  let H := G.induce (Set.univ : Set (Fin V))
  let e := induceUnivIso G
  have sameRank : matchingEdges H=matchingEdges G := rank_eq_of_graph_iso e
  have charged := three_star_critical_pair_charge H n m pn pm (forces_of_iso e.symm force)
    (by omega) crit
  omega

/-- The same arbitrary-length conclusion with the two colors interchanged. -/
theorem erdos561_nonbinary_against_three {s : ℕ} (hs : 0<s)
    (n : Fin s→ℕ) (m : Fin 3→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (big : ∃i,3≤n i) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (s+3),diagonal n m k := by
  apply exact_of_forcing_lower
  intro N G force
  have bound := sizeRamsey_le_of_host _ _ _ (forces_swap force)
  rw [erdos561_three_against_nonbinary hs m n hm hn pm pn big] at bound
  simpa only [Nat.add_comm 3 s,diagonal_swap m n] using bound

/-- Every three-star pair, with arbitrary positive nonincreasing demands
on both sides, satisfies the original antidiagonal equality. -/
theorem erdos561_three_by_three (n m : Fin 3→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) :
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (3+3),diagonal n m k := by
  by_cases bn : ∀i,n i≤2
  · by_cases bm : ∀i,m i≤2
    · exact all_binary_sizeRamsey (by decide) (by decide) n m hn hm pn pm bn bm
    · push Not at bm
      exact erdos561_three_against_nonbinary (by decide) n m hn hm pn pm bm
  · push Not at bn
    exact erdos561_nonbinary_against_three (by decide) n m hn hm pn pm bn

#print axioms critical_half_orders_off_cover
#print axioms three_star_critical_pair_charge
#print axioms erdos561_three_against_nonbinary
#print axioms erdos561_nonbinary_against_three
#print axioms erdos561_three_by_three
end JSP452Audit.StarHost


