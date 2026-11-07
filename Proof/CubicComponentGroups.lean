import CubicWhiteComponents
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

structure CubicSquareSite (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent) : Prop where
  size : (cubicWhiteSite G U c).ncard=4
  degree : ∀x∈cubicWhiteSite G U c,fourWhiteDegree G U x=2
  repair : ∀v∈cubicWhiteSite G U c,∃w∈cubicWhiteSite G U c,∀x∈cubicWhiteSite G U c,
    x≠v → x=w ∨ G.Adj x w

theorem indexed_square_site (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (v:Fin 4 ↪ X) (span:Set.range v=cubicWhiteSite G U c)
    (edges:∀i j,(cycleGraph 4).Adj i j ↔ G.Adj (v i) (v j))
    (small:∀x∈U,fourWhiteDegree G U x≤2) : CubicSquareSite G U c := by
  have inner (i:Fin 4) : v i∈cubicWhiteSite G U c := span ▸ Set.mem_range_self i
  have two : ∀i:Fin 4,∃j k:Fin 4,j≠k ∧ (cycleGraph 4).Adj i j ∧ (cycleGraph 4).Adj i k := by
    simp only [cycleGraph_adj'];decide
  have repair : ∀i:Fin 4,∃j:Fin 4,∀k:Fin 4,k≠i → k=j ∨ (cycleGraph 4).Adj k j := by
    simp only [cycleGraph_adj'];decide
  constructor
  · rw [←span,Set.ncard_range_of_injective v.injective,Nat.card_fin]
  · intro x hx
    rw [←span] at hx
    obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,k,diff,l,r⟩ := two i
    have high := small _ (site_in_white G U c (inner i))
    by_contra! neq
    have low : (G.neighborSet (v i)∩U).ncard≤1 := by change fourWhiteDegree G U (v i)≤1;omega
    have opposite := (Set.ncard_le_one (Set.toFinite _)).mp low
      (v j) ⟨(edges i j).1 l,site_in_white G U c (inner j)⟩
      (v k) ⟨(edges i k).1 r,site_in_white G U c (inner k)⟩
    exact diff (v.injective opposite)
  · intro x hx
    rw [←span] at hx;obtain ⟨i,rfl⟩ := hx
    obtain ⟨j,ok⟩ := repair i
    refine ⟨v j,inner j,?_⟩
    intro y hy ne
    rw [←span] at hy;obtain ⟨k,rfl⟩ := hy
    rcases ok k (fun eq => ne (congrArg v eq)) with eq|edge
    · exact Or.inl (congrArg v eq)
    · exact Or.inr ((edges k j).1 edge)

private theorem prefix_path {n k : ℕ} (fit:k≤n) (i j:Fin k) (adj:(pathGraph k).Adj i j) :
    (pathGraph n).Adj ((Fin.castLEEmb fit) i) ((Fin.castLEEmb fit) j) :=
  pathGraph_adj.mpr (show i.val+1=j.val ∨ j.val+1=i.val from pathGraph_adj.mp adj)

namespace CubicPairFamily
variable {I:Type*} [Fintype I] (P:CubicPairFamily X I)

theorem path_component_pays {n:ℕ} (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (v:Fin n ↪ X) (span:Set.range v=cubicWhiteSite G U c) (enough:3≤n)
    (edges:∀i j,(pathGraph n).Adj i j ↔ G.Adj (v i) (v j))
    (degree:∀x∈U,fourWhiteDegree G U x≤2) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3) :
    P.PaidRemoval G U := by
  let z : Fin n := ⟨0,by omega⟩
  let o : Fin n := ⟨1,by omega⟩
  have mem (i:Fin n) : v i∈cubicWhiteSite G U c := span ▸ Set.mem_range_self i
  have closed : G.neighborSet (v z)∩U⊆{v o} := by
    intro x hx
    have seen := site_closed_adj G U c (mem z) hx.2 hx.1
    rw [←span] at seen
    obtain ⟨j,rfl⟩ := seen
    have ij := pathGraph_adj.mp ((edges z j).2 hx.1)
    have zero : z.val=0 := rfl
    have first : j=o := Fin.ext (by change j.val=1;omega)
    exact congrArg v first
  have endDeg : fourWhiteDegree G U (v z)≤1 :=
    (Set.ncard_le_ncard closed).trans_eq (Set.ncard_singleton _)
  let w := (Fin.castLEEmb enough).trans v
  exact P.end_three_path_pays G U w (fun i => site_in_white G U c (mem _))
    (fun i j e => (edges _ _).1 (prefix_path enough i j e)) endDeg degree cap

theorem cycle_component_step {n:ℕ} (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (v:Fin n ↪ X) (span:Set.range v=cubicWhiteSite G U c) (enough:3≤n)
    (edges:∀i j,(cycleGraph n).Adj i j ↔ G.Adj (v i) (v j))
    (degree:∀x∈U,fourWhiteDegree G U x≤2) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3) :
    P.PaidRemoval G U ∨ CubicSquareSite G U c := by
  have mem (i:Fin n) : v i∈U := site_in_white G U c (span ▸ Set.mem_range_self i)
  have path (i j:Fin n) (adj:(pathGraph n).Adj i j) : G.Adj (v i) (v j) :=
    (edges i j).1 (pathGraph_le_cycleGraph adj)
  by_cases big : 6≤n
  · let w := (Fin.castLEEmb big).trans v
    exact Or.inl (P.six_path_pays G U w (fun i => mem _)
      (fun i j e => path _ _ (prefix_path big i j e)) degree cap)
  by_cases four : n=4
  · subst n;exact Or.inr (indexed_square_site G U c v span edges degree)
  have count : n=3 ∨ n=5 := by omega
  apply Or.inl
  apply P.short_closed_path_pays G U v mem path count _ cap
  rw [span];exact site_cross_zero G U c

theorem paid_or_square_at_degree_two (G:SimpleGraph X) (U:Set X) (x:U) (active:2≤fourWhiteDegree G U x.val)
    (degree:∀v∈U,fourWhiteDegree G U v≤2) (cap:∀v∈U,fourWhiteDegree G U v+P.degree U v≤3) :
    P.PaidRemoval G U ∨ CubicSquareSite G U ((G.induce U).connectedComponentMk x) := by
  let c := (G.induce U).connectedComponentMk x
  have size := site_neighbor_bound G U c x (show x∈c.supp from rfl)
  have many : 3≤Nat.card c.supp := by omega
  have orig (u:U) : Nat.card ((G.induce U).neighborSet u)≤2 := by
    rw [induced_degree_intersection];exact degree u.val u.property
  rcases degree_two_component_classification (G.induce U) orig c with path|cycle
  · obtain ⟨e⟩ := path
    obtain ⟨v,span,edge⟩ := component_path_labels G U c _ e
    exact Or.inl (P.path_component_pays G U c v span many edge degree cap)
  · obtain ⟨_,⟨e⟩⟩ := cycle
    obtain ⟨v,span,edge⟩ := component_path_labels G U c _ e
    exact P.cycle_component_step G U c v span many edge degree cap

end CubicPairFamily
#print axioms indexed_square_site
#print axioms CubicPairFamily.paid_or_square_at_degree_two
end JSP452Audit.StarHost
