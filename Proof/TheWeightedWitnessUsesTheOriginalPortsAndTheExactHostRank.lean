import EveryNeighboringRootHasADistinctCoreInTheSameTightFamily
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] (G:SimpleGraph X)

def originalPortIncidence (S:Set X) (x:X) (c:(G.induce Sᶜ).ConnectedComponent) : Prop :=
  x∈S ∧ ∃z:c.supp,G.Adj x z.val.val

theorem neighboring_roots_are_original_labels (S:Set X) (T:Set (G.induce Sᶜ).ConnectedComponent) :
    rootNeighbors (originalPortIncidence G S) T=regionRoots G S T := by
  ext x;constructor
  · rintro ⟨c,ct,inside,edge⟩;exact ⟨⟨x,inside⟩,⟨c,ct,edge⟩,rfl⟩
  · rintro ⟨a,⟨c,ct,edge⟩,rfl⟩;exact ⟨c,ct,a.property,edge⟩

noncomputable abbrev rootScale (D k c:ℕ) (x:X) := k+c*(D-Nat.card (G.neighborSet x))
theorem root_slots_count_original_deficit (D k c:ℕ) (A:Set X) (cap:∀x,Nat.card (G.neighborSet x)≤D) :
    rootSlotCount A (rootScale G D k c)=k*A.ncard+c*rootShortfall G A D := by
  classical
  let _ := Fintype.ofFinite A
  have exact := root_shortfall_sum G D A (fun x _ => cap x)
  have expand : (∑x∈A.toFinite.toFinset,(D-Nat.card (G.neighborSet x)))=∑a:↥A,(D-Nat.card (G.neighborSet a.val)) :=
    Finset.sum_subtype A.toFinite.toFinset (fun _ => A.toFinite.mem_toFinset)
      (fun x => D-Nat.card (G.neighborSet x))
  rw [expand] at exact
  rw [count_full_root_slots]
  dsimp only [rootScale]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←exact,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
    ←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Nat.mul_comm A.ncard k]

theorem actual_weighted_core_set (D k c:ℕ) (live:0<k) (cap:∀x,Nat.card (G.neighborSet x)≤D)
    (S:Set X) (tight:IsTightBarrier G S) (H:Set (G.induce Sᶜ).ConnectedComponent)
    (full:∀Q∈H,allFullComponent G S D Q) (odd:∀Q∈H,Odd (Nat.card Q.supp)) :
    let L := originalPortIncidence G S
    let w := rootScale G D k c
    let d := scaledCoreDeficit L w k H
    ∃J⊆H,let A := regionRoots G S J
      let C := regionCore G S J
      let O := regionRest G S J
      k*J.ncard=k*A.ncard+c*rootShortfall G A D+d ∧
      (∃f:↥A↪↥J,∀a,L a.val (f a).val) ∧
      (∀x∈C,Nat.card (G.neighborSet x)=D) ∧ (∀x∈C,∀y∈O,¬G.Adj x y) ∧
      C.ncard=2*matchingEdges (G.induce C)+J.ncard ∧
      matchingEdges G=A.ncard+matchingEdges (G.induce C)+matchingEdges (G.induce O) := by
  intro L w d
  obtain ⟨_,J,sub,att,_⟩ := actual_scaled_hall_witness L w k live H
  have assignment := tight_slot_actual_root_matching L w k live (fun x => Nat.le_add_right _ _) H J sub att
  have labels : rootNeighbors L J=regionRoots G S J := neighboring_roots_are_original_labels G S J
  rw [labels] at assignment att
  change k*J.ncard=rootSlotCount (regionRoots G S J) (rootScale G D k c)+d at att
  rw [root_slots_count_original_deficit G D k c _ cap] at att
  exact ⟨J,sub,att,assignment,fun _ m => regionCore_full_degree G S J D (fun Q mem => full Q (sub mem)) m,
    fun _ m _ n => no_edge_core_rest G S J m n,core_order_matching G S tight J (fun Q mem => odd Q (sub mem)),
    region_rank_partition G S tight J⟩

#print axioms neighboring_roots_are_original_labels
#print axioms root_slots_count_original_deficit
#print axioms actual_weighted_core_set
end JSP452Audit.StarHost
