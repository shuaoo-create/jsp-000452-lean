import GoodFullAllocation
import FreeBadPortIncidence

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Hall bound for any chosen family of small full cliques, using only its own adjacent roots. -/
theorem barrier_full_cliques_hall {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (pos : 0<D) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (B : Set (G.induce Sᶜ).ConnectedComponent) (allFull : ∀ c∈B, allFullComponent G S D c)
    (all : ∀ c ∈ B, ((G.induce Sᶜ).induce c.supp)=⊤ ∧ Nat.card c.supp ≤ D) :
    B.ncard ≤ (rootNeighbors (rootIncidence G S) B).ncard := by
  classical
  let I := ↥B
  let _ := Fintype.ofFinite I
  let C (i : I) : Set X := Subtype.val '' i.val.supp
  have card (i : I) : (C i).ncard = Nat.card i.val.supp :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have apart (i j : I) (ne : i≠j) : Disjoint (C i) (C j) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,e⟩
    have eq : b=a := Subtype.ext e
    have ha' : (G.induce Sᶜ).connectedComponentMk a=i.val := ha
    have hb' : (G.induce Sᶜ).connectedComponentMk b=j.val := hb
    exact ne (Subtype.ext (ha'.symm.trans (eq ▸ hb')))
  have clique (i : I) : G.IsClique (C i) := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ ne
    let v : i.val.supp := ⟨a,ha⟩
    let w : i.val.supp := ⟨b,hb⟩
    change ((G.induce Sᶜ).induce i.val.supp).Adj v w
    rw [(all i.val i.property).1]
    exact fun eq => ne (congrArg (fun p : i.val.supp => p.val.val) eq)
  have full (i : I) (x : X) (hx : x∈C i) : Nat.card (G.neighborSet x) = D := by
    rcases hx with ⟨a,ha,rfl⟩
    exact allFull i.val i.property ⟨a,ha⟩
  have positive (i : I) : 1 ≤ (C i).ncard := by
    let _ : Nonempty i.val.supp := i.val.nonempty_supp.to_subtype
    rw [card]; exact Nat.card_pos
  have external (i : I) (x : X) (hx : x∈C i) (y : X) (edge : G.Adj x y) (out : y∉C i) :
      y∈regionRoots G S B := by
    rcases hx with ⟨a,ha,rfl⟩
    by_cases hy : y∈S
    · exact ⟨⟨y,hy⟩,⟨i.val,i.property,⟨a,ha⟩,edge.symm⟩,rfl⟩
    · let b : ↥Sᶜ := ⟨y,hy⟩
      have adj : (G.induce Sᶜ).Adj a b := edge
      exact (out ⟨b,(i.val.mem_supp_congr_adj adj).mp ha,rfl⟩).elim
  have bounded := clique_family_le_roots G C (regionRoots G S B) D pos apart clique full positive
    (fun i => (card i).le.trans (all i.val i.property).2) external (fun x _ => cap x)
  change B.ncard ≤ (regionRoots G S B).ncard at bounded
  have nroot : (regionRoots G S B).ncard = (rootNeighbors (rootIncidence G S) B).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  exact bounded.trans_eq nroot


theorem odd_goodFull_hall {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (odd : Odd D) (cap : ∀ x,Nat.card (G.neighborSet x)≤D)
    (critical : ∀ c : (G.induce Sᶜ).ConnectedComponent, PerfectAfterEveryDeletion c.toSimpleGraph)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (sub : T ⊆ goodFullClass G S D) :
    T.ncard ≤ (rootNeighbors (rootIncidence G S) T).ncard := by
  have parity := Nat.odd_iff.mp odd
  apply barrier_full_cliques_hall G S D (by omega) cap T (fun c hc => (sub hc).1)
  intro c hc
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  have bound (v : c.supp) : Nat.card (c.toSimpleGraph.neighborSet v) ≤ D :=
    (induced_neighbor_count_le (G.induce Sᶜ) c.supp v).trans
      ((induced_neighbor_count_le G Sᶜ v.val).trans (cap _))
  exact odd_good_component_is_small_clique c.toSimpleGraph D odd bound (critical c) (sub hc).2

/-- The Hall bound removes the entire good-class deficit on the very same minimizing allocation. -/
theorem odd_goodFull_saturated {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (odd : Odd D) (cap : ∀ x,Nat.card (G.neighborSet x)≤D)
    (critical : ∀ c : (G.induce Sᶜ).ConnectedComponent, PerfectAfterEveryDeletion c.toSimpleGraph)
    (A : RootAllocation G S) (T : Set (G.induce Sᶜ).ConnectedComponent) (sub : T⊆goodFullClass G S D)
    (eq : T.ncard = (rootNeighbors (rootIncidence G S) T).ncard +
      (goodFullClass G S D \ Set.range A.place).ncard) :
    (goodFullClass G S D \ Set.range A.place).ncard=0 := by
  have pay := odd_goodFull_hall G S D odd cap critical T sub
  omega

/-- In odd degree the full exposure is exactly the number of genuinely bad unassigned components. -/
theorem exists_odd_bad_assignment {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (odd : Odd D) (cap : ∀ x,Nat.card (G.neighborSet x)≤D) :
    ∃ A : RootAllocation G S, goodFullClass G S D ⊆ Set.range A.place ∧
      freeFull G S D A = badFree G S D A ∧ (badFree G S D A).ncard = minimumExposure G D := by
  classical
  obtain ⟨A,T,sub,free,eq,_⟩ := optimal_good_port_allocation G S tight data D
  have zero := odd_goodFull_saturated G S D odd cap (fun c => (data c).2) A T sub eq
  have assigned : goodFullClass G S D ⊆ Set.range A.place := by
    intro c hc
    by_contra miss
    have positive := (Set.ncard_pos (s := goodFullClass G S D \ Set.range A.place)).mpr
      (show (goodFullClass G S D \ Set.range A.place).Nonempty from ⟨c,hc,miss⟩)
    omega
  have same : freeFull G S D A = badFree G S D A := by
    ext c
    exact ⟨fun h => ⟨h,fun good => h.1 (assigned ⟨h.2,good⟩)⟩, fun h => h.1⟩
  exact ⟨A,assigned,same,same ▸ free⟩

#print axioms odd_goodFull_hall
#print axioms odd_goodFull_saturated
#print axioms exists_odd_bad_assignment
end JSP452Audit.StarHost
