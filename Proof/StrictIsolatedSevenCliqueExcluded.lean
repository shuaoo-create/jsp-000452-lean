import SevenCliqueSimulatedAtFive
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_no_isolated_seven_clique (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (six : diagonal F.n F.m (F.r+2)-1=6) (U:Set F.X) (closed:∀v∈U,∀w,F.G.Adj v w → w∈U)
    (iso : F.G.induce U ≃g sevenComplete) : False := by
  let B := F.G.induce Uᶜ
  let old := B ⊕g sevenComplete
  let newG := B ⊕g forest sevenStarLeaves
  let join := regionSumIso F.G Set.univ Uᶜ U (Set.compl_union_self _) disjoint_compl_left
    (fun x hx y hy edge => hx (closed y hy x edge.symm))
  let e : F.G ≃g old := (join.trans (induceUnivIso F.G)).symm.trans (Iso.sumCongr (Iso.refl : B ≃g B) iso)
  have edgeOld : F.G.edgeSet.ncard=old.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  change F.G.edgeSet.ncard=(B ⊕g sevenComplete).edgeSet.ncard at edgeOld
  rw [edge_ncard_sumGraph,seven_clique_edge_price] at edgeOld
  have edgeNew : newG.edgeSet.ncard=B.edgeSet.ncard+20 := by
    change (B ⊕g forest sevenStarLeaves).edgeSet.ncard=_
    rw [edge_ncard_sumGraph,four_star_edge_price]
  obtain ⟨ncap,mcap,_⟩ := strict_only_double_escape F paid
  have hn (i:Fin F.s) : F.n i≤5 := by have hi := ncap i;rw [six] at hi;omega
  have hm (j:Fin F.t) : F.m j≤5 := by have hi := mcap j;rw [six] at hi;omega
  have row := substitute_fixed_exterior_row B sevenComplete (forest sevenStarLeaves) 5
    seven_clique_simulated_at_five F.n F.m F.pn F.pm hn hm (forcingRow_of_iso e F.row)
  have smaller : newG.edgeSet.ncard<F.G.edgeSet.ncard := by omega
  let T : StrictFamily.{u} := { F with X := _, G := newG, finiteX := inferInstance, row := row, strict := smaller.trans F.strict }
  have equal := (minimal_rank_exact_source T (show AllSmallerPaid.{u} T.rank from paid)).2.1
  change newG.edgeSet.ncard+1=rowEnergy F.n F.m F.r at equal
  have earlier := (minimal_rank_exact_source F paid).2.1
  omega

theorem order_seven_regular_iso {X:Type*} [Finite X] (C:SimpleGraph X) (order:Nat.card X=7)
    (regular:∀v,Nat.card (C.neighborSet v)=6) : Nonempty (C ≃g sevenComplete) := by
  classical
  let _ := Fintype.ofFinite X
  let e := Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans order)
  have all (x:X) : C.neighborSet x=({x} : Set X)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le (ht:=Set.toFinite _)
    · intro y hy
      exact fun mem => (C.ne_of_adj hy) (Set.mem_singleton_iff.mp mem).symm
    · have total := Set.ncard_add_ncard_compl ({x} : Set X)
      rw [Set.ncard_singleton,order] at total
      rw [←Nat.card_coe_set_eq (C.neighborSet x),regular]
      omega
  refine ⟨{toEquiv := e,map_rel_iff' := ?_}⟩
  intro x y
  change e x≠e y ↔ C.Adj x y
  rw [e.injective.ne_iff]
  have eq : C.Adj x y ↔ y∈({x}:Set X)ᶜ := by change y∈C.neighborSet x ↔ _;rw [all]
  rw [eq]
  exact ne_comm

theorem strict_six_odd_regular_order (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six : diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (mem:c∈oddRegularComponents F.G 6) :
    9≤Nat.card c.supp := by
  obtain ⟨⟨k,odd⟩,reg⟩ := mem
  let v := c.nonempty_supp.to_subtype.some
  have localReg (x:c.supp) := (component_degree_eq F.G c x).trans (reg x.val x.property)
  have subset : c.toSimpleGraph.neighborSet v⊆({v}:Set c.supp)ᶜ :=
    fun _ h mem => c.toSimpleGraph.ne_of_adj h (Set.mem_singleton_iff.mp mem).symm
  have size := Set.ncard_le_ncard subset
  rw [←Nat.card_coe_set_eq,localReg] at size
  have total := Set.ncard_add_ncard_compl ({v}:Set c.supp)
  rw [Set.ncard_singleton] at total
  have notSeven (eq:Nat.card c.supp=7) : False := by
    obtain ⟨iso⟩ := order_seven_regular_iso c.toSimpleGraph eq localReg
    exact strict_no_isolated_seven_clique F paid six c.supp (fun _ hx _ e => (c.mem_supp_congr_adj e).mp hx) iso
  change Nat.card c.supp=2*k+1 at odd
  by_contra! tiny
  apply notSeven
  clear * - odd size total tiny
  omega

#print axioms strict_no_isolated_seven_clique
#print axioms order_seven_regular_iso
#print axioms strict_six_odd_regular_order
end JSP452Audit.StarHost
