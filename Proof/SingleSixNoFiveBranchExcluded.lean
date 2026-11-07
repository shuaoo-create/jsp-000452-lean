import OriginalMenuPaysFifthColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem single_no_five_history_contradiction (P r C b k L M N f:ℕ)
    (capacity:4≤P) (ks:k=P-(r+1)) (small:2*N≤P) (large:3*M≤2*P+1)
    (shadow:L≤b+N) (nested:b≤C)
    (five:P+4+min k C+min k b≤k+L+1)
    (six:4+min k C+min k b≤2*k+1)
    (fifth:2*P+4+min k C+min k b≤min (k+P) f+L+1)
    (profile:f≤max (2*N) (C+6+M)) : False := by
  by_cases all:k≤b
  · rw [min_eq_left all,min_eq_left (all.trans nested)] at six;omega
  have short := Nat.le_of_not_ge all
  rw [min_eq_right short] at five fifth
  by_cases finish:k≤C
  · rw [min_eq_left finish] at five;omega
  · rw [min_eq_right (Nat.le_of_not_ge finish)] at fifth
    omega

theorem strict_six_no_five_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4) : False := by
  classical
  obtain ⟨h,cards,_⟩ := strict_six_only_one_original_component F paid six
  have non : (oddRegularComponents F.G 6).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨c,member⟩ := non
  let e : Fin 1 ↪ F.G.ConnectedComponent := ⟨fun _ => c,fun _ _ _ => Subsingleton.elim _ _⟩
  let T := Finset.univ.map e
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let P := matchingEdges (F.G.induce U)
  let d := F.rank-matchingEdges F.G
  let k := P-(F.r+1)
  let L := widthAt F.n F.m F.r 6
  let M := chosenSlots F.G T 2
  let N := chosenSlots F.G T 3
  have elems (v) (mem:v∈T) : v∈oddRegularComponents F.G 6 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp mem;exact member
  have card : T.card=1 := by simp [T]
  have rank := (component_union_accounts F.G T).2.1
  change P=∑v∈Finset.univ.map e,matchingEdges v.toSimpleGraph at rank
  rw [Finset.sum_map] at rank
  have simple : P=matchingEdges c.toSimpleGraph := by rw [rank,Fin.sum_univ_one];rfl
  have cap := (strict_six_true_component_capacity F paid six c member).1
  have price := (strict_six_chosen_edge_price F paid six T elems).2 red blue
  rw [card,h] at price
  change 5*P+3*1+1≤d+1+4*(P+(1-1)/2)+N+(1-1) at price
  obtain ⟨m,n⟩ := strict_chosen_slot_totals F paid six T elems
  change 3*M≤2*P+T.card at m
  rw [card] at m
  change 2*N≤P at n
  have dp : P≤2*d := by omega
  obtain ⟨H⟩ := six_five_four_history_exists O
  have floor := (strict_exterior_history_cut_bounds F paid six T elems H).1
  change 2*d≤H.fourCut.ncard at floor
  have fit : k≤H.fourCut.ncard := by dsimp only [k];omega
  have menu := split_capacities_of_small (fun i:Fin 1 => matchingEdges (e i).toSimpleGraph) (F.r+k)
    (fun i => by change matchingEdges c.toSimpleGraph≤F.r+k+1;dsimp only [k];omega)
  obtain ⟨p5,p6⟩ := strict_six_menu_history_price F paid six e (fun _ => member) k menu H fit
  have p4 := strict_six_fifth_menu_price F paid six e (fun _ => member) k menu H fit
  rw [←rank,Fintype.card_fin,h] at p5 p4
  rw [Fintype.card_fin,h] at p6
  obtain ⟨A,inside⟩ := complete_degree_stage_exists (F.G.induce U) 6
  have shadow := (strict_no_five_exterior_full_stage F paid six red blue T A H.six inside H.stageSix).2.2
  have nested : H.six.ncard≤H.fiveCut.ncard := by rw [H.cut_counts.1];omega
  have profile := strict_no_five_actual_fifth_column F paid six red blue T H
  exact single_no_five_history_contradiction P F.r H.fiveCut.ncard H.six.ncard k L M N (widthAt F.n F.m F.r 5)
    (simple.symm ▸ cap) rfl n m shadow nested p5 p6 p4 profile

#print axioms single_no_five_history_contradiction
#print axioms strict_six_no_five_impossible
end JSP452Audit.StarHost
