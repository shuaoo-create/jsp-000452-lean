import IdentifyPhysicalNineVertexHost
namespace JSP452Audit.StarHost
open SimpleGraph

def nineLabel (x:Fin 3×Fin 3) : ℕ := 3*x.1.val+x.2.val
def cyclePairs : Finset (ℕ×ℕ) :=
  {(0,3),(3,1),(1,6),(6,0),(2,4),(4,7),(7,5),(5,8),(8,2)}
abbrev cycleRel (x y:Fin 3×Fin 3) : Prop := (nineLabel x,nineLabel y)∈cyclePairs
def twoCycleColor : SimpleGraph (Fin 3×Fin 3) := fromRel cycleRel
def fourCycleVertices : Finset (Fin 3×Fin 3) :=
  Finset.univ.filter (fun x => nineLabel x∈({0,3,1,6}:Finset ℕ))

abbrev redRelation (x y:Fin 3×Fin 3) := x≠y ∧ (cycleRel x y ∨ cycleRel y x)
abbrev blueRelation (x y:Fin 3×Fin 3) := x.1≠y.1 ∧ ¬redRelation x y

private theorem color_table_sub : ∀x y:Fin 3×Fin 3,redRelation x y → x.1≠y.1 := by decide +kernel
private theorem color_table_cut : ∀x y:Fin 3×Fin 3,x∈fourCycleVertices → redRelation x y → y∈fourCycleVertices := by decide +kernel
private theorem color_table_cap : ∀x:Fin 3×Fin 3,(Finset.univ.filter (blueRelation x)).card≤4 := by decide +kernel

theorem two_cycle_palette_on_nine :
    twoCycleColor≤threeByThreeHost ∧ UniformPackCap twoCycleColor 2 2 ∧
      UniformPackCap (threeByThreeHost \ twoCycleColor) 5 0 := by
  let X := Fin 3×Fin 3
  have sub := color_table_sub
  let V : Set X := fourCycleVertices
  have size : fourCycleVertices.card=4 := by decide +kernel
  have order : V.ncard=4 := (Set.ncard_coe_finset _).trans size
  have total := Set.ncard_add_ncard_compl V
  have universeSize : Nat.card X=9 := by change Nat.card (Fin 3×Fin 3)=9;simp [Nat.card_prod]
  have other : Vᶜ.ncard=5 := by omega
  have check := color_table_cut
  have closed (x:X) (hx:x∈V) (y:X) (edge:twoCycleColor.Adj x y) : y∈V := check x y hx edge
  have caps := color_table_cap
  have deg (x:X) : Nat.card ((threeByThreeHost \ twoCycleColor).neighborSet x)<5 := by
    have eq : (threeByThreeHost \ twoCycleColor).neighborSet x=(↑(Finset.univ.filter (blueRelation x)):Set X) := by
      ext y;change blueRelation x y ↔ y∈Finset.univ.filter (blueRelation x);simp
    rw [eq,Nat.card_coe_set_eq,Set.ncard_coe_finset]
    have := caps x;omega
  refine ⟨sub,?_,uniform_pack_below_degree _ 5 deg⟩
  intro k copy
  let e : twoCycleColor.induce V⊕g twoCycleColor.induce Vᶜ ≃g twoCycleColor := (regionSumIso twoCycleColor Set.univ V Vᶜ (Set.union_compl_self _) disjoint_compl_right
    (fun x hx y hy edge => hy (closed x hx y edge))).trans (induceUnivIso twoCycleColor)
  obtain ⟨f⟩ := copy
  obtain ⟨a,b,split,left,right⟩ := uniform_copy_split_sum (twoCycleColor.induce V) (twoCycleColor.induce Vᶜ) 2 k
    ⟨e.symm.toCopy.comp f⟩
  have first := uniform_pack_order_cap (twoCycleColor.induce V) 2 (by decide) Set.univ (fun _ _ _ => Set.mem_univ _) a left
  have second := uniform_pack_order_cap (twoCycleColor.induce Vᶜ) 2 (by decide) Set.univ (fun _ _ _ => Set.mem_univ _) b right
  rw [Set.ncard_univ] at first second
  change a≤V.ncard/3 at first
  change b≤Vᶜ.ncard/3 at second
  omega

#print axioms two_cycle_palette_on_nine
end JSP452Audit.StarHost
