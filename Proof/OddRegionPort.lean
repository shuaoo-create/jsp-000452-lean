import OddGoodComponents
import ActualLowPort
import RegionCliqueObstruction
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def internallyGood (Q : SimpleGraph X) (D : ℕ) : Prop :=
  ∀ y∈portLow Q D,GoodPort Q y

/-- The true neighborhood in the original barrier supports every subset
of all-good full components in odd degree. -/
theorem odd_good_hall (G : SimpleGraph X) (D : ℕ) (odd : Odd D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (K : DegreeRegion G D)
    (B : Set (G.induce K.barrierᶜ).ConnectedComponent) (sub : B⊆K.pieces)
    (good : ∀c∈B,internallyGood ((G.induce K.barrierᶜ).induce c.supp) D) :
    B.ncard≤(rootNeighbors (rootIncidence G K.barrier) B).ncard := by
  have parity := Nat.odd_iff.mp odd
  apply region_cliques_hall G D (by omega) cap K B sub
  intro c hc
  exact region_good_piece_odd_clique G D K odd cap c (good c hc)

theorem odd_bad_component_count (G : SimpleGraph X) (D : ℕ) (odd : Odd D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (K : DegreeRegion G D) :
    minimumExposure G D ≤
      {c ∈ K.pieces | ¬internallyGood ((G.induce K.barrierᶜ).induce c.supp) D}.ncard := by
  classical
  let good : Set (G.induce K.barrierᶜ).ConnectedComponent :=
    {c ∈ K.pieces | internallyGood ((G.induce K.barrierᶜ).induce c.supp) D}
  have sub : good⊆K.pieces := fun _ h => h.1
  have bound := odd_good_hall G D odd cap K good sub (fun _ h => h.2)
  have nbr : rootNeighbors (rootIncidence G K.barrier) good ⊆ rootNeighbors (rootIncidence G K.barrier) K.pieces := by
    rintro r ⟨c,hc,edge⟩
    exact ⟨c,sub hc,edge⟩
  have ct := Set.ncard_le_ncard nbr
  have total := Set.ncard_sdiff_add_ncard_of_subset sub
  have diff : K.pieces \ good = {c ∈ K.pieces | ¬internallyGood ((G.induce K.barrierᶜ).induce c.supp) D} := by
    ext c
    change (_ ∧ ¬(_ ∧ _)) ↔ (_ ∧ ¬_)
    tauto
  rw [diff] at total
  have bal := K.balanced
  omega

/-- An actual adjacent root and the internal near-perfect matching which
witnesses the failure of goodness, in the original deficient region. -/
theorem exposed_odd_region_has_bad_port (G : SimpleGraph X) (D : ℕ) (odd : Odd D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (K : DegreeRegion G D)
    (positive : 0<minimumExposure G D) :
    ∃ c∈K.pieces, ∃ y : c.supp, ∃ r∈K.roots, G.Adj r y.val.val ∧
      (let Q := (G.induce K.barrierᶜ).induce c.supp
       y∈portLow Q D ∧ ∃v, v≠y ∧ ∃ M : Q.Subgraph, M.IsMatching ∧ M.verts={a|a≠v} ∧
          ∃z,M.Adj y z ∧ ¬Q.Adj v z) := by
  classical
  have count := odd_bad_component_count G D odd cap K
  obtain ⟨c,hc,bad⟩ := Set.nonempty_of_ncard_ne_zero (by omega : {t ∈ K.pieces | ¬internallyGood ((G.induce K.barrierᶜ).induce t.supp) D}.ncard≠0)
  unfold internallyGood at bad
  push Not at bad
  obtain ⟨y,low,bad⟩ := bad
  obtain ⟨r,root,edge⟩ := internal_low_adjacent_root G D K c hc y low
  exact ⟨c,hc,y,r,root,edge,low,not_good_port_witness _ y bad⟩

#print axioms odd_good_hall
#print axioms odd_bad_component_count
#print axioms exposed_odd_region_has_bad_port
end JSP452Audit.StarHost
