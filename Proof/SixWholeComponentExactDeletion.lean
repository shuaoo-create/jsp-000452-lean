import OriginalComponentEdgeMenus
open private JSP452Audit.StarHost.piece_sup_adj from WholeComponentPieces
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem original_whole_menu_row {I X:Type*} [Fintype I] [DecidableEq I] [Finite X]
    (G:SimpleGraph X) (e:I ↪ G.ConnectedComponent) (V:Set X) {s t r:ℕ} (n m:ℕ→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i<s,0<n i) (pm:∀j<t,0<m j)
    (menu:SplitCapacities (fun i => matchingEdges (e i).toSimpleGraph) (r+V.ncard))
    (row:ForcingRow G s t n m r) :
    let H := Finset.univ.sup (fun i => labelledPart G (e i))
    ForcingRow ((G \ H).induce Vᶜ) s t n m (r+V.ncard+∑i,matchingEdges (e i).toSimpleGraph) := by
  exact actual_piece_menu_of_splits G V (fun i => labelledPart G (e i)) (fun i => matchingEdges (e i).toSimpleGraph)
    n m hn hm pn pm (fun _ _ _ edge => edge.1) (fun T => (original_component_menu_accounts G e T).1.le) menu row

theorem strict_six_no_full_degree_menu {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (six:diagonal F.n F.m (F.r+2)-1=6)
    (e:I ↪ F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 6) (V:Set F.X)
    (menu:SplitCapacities (fun i => matchingEdges (e i).toSimpleGraph) (F.r+V.ncard))
    (ind:F.G.IsIndepSet V) (full:∀v∈V,Nat.card (F.G.neighborSet v)=6) (away:∀i,Disjoint (e i).supp V) :
    3*Fintype.card I<highestWidth F.n F.m F.r := by
  classical
  let part := fun i => labelledPart F.G (e i)
  let H := Finset.univ.sup part
  let z := fun i => matchingEdges (e i).toSimpleGraph
  let P := ∑i,z i
  let Y := (F.G \ H).induce Vᶜ
  have row := original_whole_menu_row F.G e V _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) menu F.row
  have sub : H≤F.G := Finset.sup_le (fun i _ _ _ edge => edge.1)
  have off {x y:F.X} (edge:H.Adj x y) : x∉V := by
    obtain ⟨i,_,mem⟩ := (JSP452Audit.StarHost.piece_sup_adj part Finset.univ x y).mp edge
    exact fun v => Set.disjoint_left.mp (away i) mem.2 v
  have saving := selected_edge_saving F.G H V 6 sub ind full (fun {_ _} edge => off edge)
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+H.edgeSet.ncard+6*V.ncard at saving
  have cost := (original_component_menu_accounts F.G e Finset.univ).2
  have each (i:I) : (e i).toSimpleGraph.edgeSet.ncard=6*z i+3 := (strict_six_true_component_capacity F paid six (e i) (actual i)).2.2.2
  change H.edgeSet.ncard=∑i,(e i).toSimpleGraph.edgeSet.ncard at cost
  simp only [each,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at cost
  change H.edgeSet.ncard=6*P+Fintype.card I*3 at cost
  let i := Classical.choice (inferInstance : Nonempty I)
  have zi := (strict_six_true_component_capacity F paid six (e i) (actual i)).1
  change 4≤z i at zi
  have key : z i≤P := Finset.single_le_sum (f:=z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have step : 0<V.ncard+P := by omega
  have natural : F.G.edgeSet.ncard=Y.edgeSet.ncard+6*(V.ncard+P)+3*Fintype.card I := by omega
  have algebra : (F.G.edgeSet.ncard:ℤ)=(Y.edgeSet.ncard:ℤ)+6*(V.ncard+P:ℕ)+(3*Fintype.card I:ℕ) := by exact_mod_cast natural
  have top : diagonal F.n F.m (F.r+2)=7 := by omega
  have price := smaller_source_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G Y F.r (V.ncard+P) 6 F.rank
    paid F.live le_rfl step top.le (by simpa [Nat.add_assoc,Y,H,part,P,z] using row) _ algebra
  rw [show 6+1=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price
  have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  omega

#print axioms original_whole_menu_row
#print axioms strict_six_no_full_degree_menu
end JSP452Audit.StarHost
