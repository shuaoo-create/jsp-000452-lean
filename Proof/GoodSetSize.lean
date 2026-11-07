import GoodPortClassification
import HallNeighborhoods
import RootCutCoverage

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} (G : SimpleGraph X) (S : Set X) (D : ℕ)
  (T B : Set (G.induce Sᶜ).ConnectedComponent)
  (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)

/-- In T choose all low labels of a split component, otherwise its specified
representative. Components outside T contribute no labels. -/
noncomputable def goodPortFiber (c : (G.induce Sᶜ).ConnectedComponent) : Set c.supp := by
  classical
  exact if c ∈ T then (if c ∈ B then portLow c.toSimpleGraph D else {pick c}) else ∅

def goodPortSet : Set X :=
  {v | ∃ (c : (G.induce Sᶜ).ConnectedComponent) (x : c.supp),
    x ∈ goodPortFiber G S D T B pick c ∧ x.val.val=v}

private theorem component_of_same_label {c d : (G.induce Sᶜ).ConnectedComponent}
    (x : c.supp) (y : d.supp) (eq : x.val.val=y.val.val) : c=d := by
  have same : x.val=y.val := Subtype.ext eq
  exact ConnectedComponent.eq_of_common_vertex x.property (same ▸ y.property)

theorem goodPortSet_member_iff (c : (G.induce Sᶜ).ConnectedComponent) (x : c.supp) :
    x.val.val ∈ goodPortSet G S D T B pick ↔ c ∈ T ∧
      ((c ∈ B ∧ x ∈ portLow c.toSimpleGraph D) ∨ (c ∉ B ∧ x=pick c)) := by
  classical
  have mem : x.val.val ∈ goodPortSet G S D T B pick ↔ x ∈ goodPortFiber G S D T B pick c := by
    refine ⟨?_,fun h => ⟨c,x,h,rfl⟩⟩
    rintro ⟨d,y,hy,eq⟩
    obtain rfl := component_of_same_label G S y x eq
    have same : y=x := Subtype.ext (Subtype.ext eq)
    exact same ▸ hy
  rw [mem]
  by_cases ht : c ∈ T <;> by_cases hb : c ∈ B <;> simp [goodPortFiber,ht,hb]

theorem goodPortSet_independent (split : ∀ c ∈ B, GoodPortSplit c.toSimpleGraph D) :
    G.IsIndepSet (goodPortSet G S D T B pick) := by
  rintro _ ⟨c,x,hx,rfl⟩ _ ⟨d,y,hy,rfl⟩ neq edge
  have same : x.val∈c.supp := x.property
  have adj : (G.induce Sᶜ).Adj x.val y.val := edge
  have yc : y.val ∈ c.supp := (c.mem_supp_congr_adj adj).mp same
  obtain rfl := ConnectedComponent.eq_of_common_vertex yc y.property
  have xset : x.val.val ∈ goodPortSet G S D T B pick := ⟨c,x,hx,rfl⟩
  have yset : y.val.val ∈ goodPortSet G S D T B pick := ⟨c,y,hy,rfl⟩
  have xcases := ((goodPortSet_member_iff G S D T B pick c x).mp xset).2
  have ycases := ((goodPortSet_member_iff G S D T B pick c y).mp yset).2
  rcases xcases with ⟨hb,xlow⟩ | ⟨hb,rfl⟩
  · rcases ycases with ⟨_,ylow⟩ | ⟨no,_⟩
    · rcases ((split c hb).join x y).mp edge with ⟨_,xf | yf⟩
      · exact (Nat.ne_of_lt xlow) xf
      · exact (Nat.ne_of_lt ylow) yf
    · exact no hb
  · rcases ycases with ⟨yes,_⟩ | ⟨_,rfl⟩
    · exact hb yes
    · exact neq rfl

theorem goodPortSet_full (full : ∀ c ∈ T, allFullComponent G S D c) :
    ∀ x ∈ goodPortSet G S D T B pick, Nat.card (G.neighborSet x) = D := by
  rintro _ ⟨c,x,hx,rfl⟩
  have mem := (goodPortSet_member_iff G S D T B pick c x).mp ⟨c,x,hx,rfl⟩
  exact full c mem.1 x

/-- A vertex incident to a barrier root misses at least that neighbor inside
its own component, hence is one of its low vertices. -/
theorem root_adjacent_port_low [Finite X] (c : (G.induce Sᶜ).ConnectedComponent)
    (x : c.supp) (a : ↥S) (edge : G.Adj a.val x.val.val)
    (cap : Nat.card (G.neighborSet x.val.val) ≤ D) : x ∈ portLow c.toSimpleGraph D := by
  have sub := induced_neighbor_count_le (G.induce Sᶜ) c.supp x
  have res := induced_neighbor_count_le G Sᶜ x.val
  change Nat.card (((G.induce Sᶜ).induce c.supp).neighborSet x) < D
  by_contra! high
  have whole : Nat.card ((G.induce Sᶜ).neighborSet x.val) = D := by omega
  exact (all_neighbors_survive_of_induced_full G Sᶜ x.val D cap whole a.val edge.symm) a.property

/-- A selected component's stored root mate belongs to the union in both
cases: it is the unique representative outside B and a genuine low vertex in B. -/
theorem goodPortSet_root_pick [Finite X] (c : (G.induce Sᶜ).ConnectedComponent) (hc : c ∈ T)
    (a : ↥S) (edge : G.Adj a.val (pick c).val.val)
    (cap : Nat.card (G.neighborSet (pick c).val.val) ≤ D) :
    (pick c).val.val ∈ goodPortSet G S D T B pick := by
  apply (goodPortSet_member_iff G S D T B pick c (pick c)).mpr
  by_cases hb : c ∈ B
  · exact ⟨hc,Or.inl ⟨hb,root_adjacent_port_low G S D c (pick c) a edge cap⟩⟩
  · exact ⟨hc,Or.inr ⟨hb,rfl⟩⟩

/-- Each actual component contributes one label, and every split component
contributes at least one further label. The dependent sum counts original
vertices without assigning separate labels to any shared vertex. -/
theorem goodPortSet_size [Finite X] (inside : B ⊆ T)
    (split : ∀ c ∈ B, GoodPortSplit c.toSimpleGraph D)
    (h rootCount : ℕ) (balance : T.ncard = rootCount + h) :
    h + rootCount + B.ncard ≤ (goodPortSet G S D T B pick).ncard := by
  classical
  let C := (G.induce Sᶜ).ConnectedComponent
  let _ := Fintype.ofFinite C
  let P := goodPortSet G S D T B pick
  let F (c : C) := goodPortFiber G S D T B pick c
  let into (s : Σ c : C, ↥(F c)) : ↥P := ⟨s.2.val.val.val, s.1,s.2.val,s.2.property,rfl⟩
  have inj : Function.Injective into := by
    rintro ⟨c,x⟩ ⟨d,y⟩ eq
    have same : x.val.val.val = y.val.val.val := congrArg (fun u : ↥P => u.val) eq
    obtain rfl := component_of_same_label G S x.val y.val same
    have xy : x = y := Subtype.ext (Subtype.ext (Subtype.ext same))
    cases xy
    rfl
  have embeds := Nat.card_le_card_of_injective into inj
  rw [Nat.card_sigma, Nat.card_coe_set_eq] at embeds
  have indicator (K : Set C) : K.ncard = ∑ c : C, (if c ∈ K then 1 else 0) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Finset.sum_boole]
    exact Fintype.card_subtype (fun c : C => c∈K)
  have term (c : C) : (if c ∈ T then 1 else 0) + (if c ∈ B then 1 else 0) ≤ Nat.card ↥(F c) := by
    by_cases hb : c ∈ B
    · simpa [F, goodPortFiber, inside hb, hb, Nat.card_coe_set_eq] using (split c hb).low_count
    · by_cases ht : c ∈ T <;> simp [F,goodPortFiber,ht,hb]
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun c _ => term c)
  rw [Finset.sum_add_distrib, ← indicator T, ← indicator B] at bound
  change _ ≤ P.ncard
  omega

#print axioms goodPortSet_member_iff
#print axioms goodPortSet_independent
#print axioms goodPortSet_full
#print axioms root_adjacent_port_low
#print axioms goodPortSet_root_pick
#print axioms goodPortSet_size
end JSP452Audit.StarHost
