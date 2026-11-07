import TheMixedNineLeafCaseProvidesEnoughActualExteriorVertices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem incident_exterior_forcing_row {X:Type u} [Finite X] (G:SimpleGraph X) (U:Set X)
    (V:Set ↥(Uᶜ:Set X)) {s t r:ℕ} (n m:ℕ→ℕ)
    (pn:∀i<s,0<n i) (pm:∀j<t,0<m j)
    (row:ForcingRow (((G \ eraseInternal G Uᶜ)).induce (Subtype.val '' V)ᶜ) s t n m r) :
    ForcingRow ((G.induce Uᶜ).induce Vᶜ) s t n m r := by
  let S := (Subtype.val '' V)ᶜ
  let Y := ((G \ eraseInternal G Uᶜ)).induce S
  let T : Set S := {v|v.val∈Uᶜ}
  have inside {a b:↥S} (edge:Y.Adj a b) : a∈T := fun h => edge.2 ⟨edge.1,fun both => both.1 h⟩
  let send (x:↥(Vᶜ:Set ↥(Uᶜ:Set X))) : T :=
    ⟨⟨x.val.val,by rintro ⟨v,hv,eq⟩;exact x.property ((Subtype.ext eq : v=x.val) ▸ hv)⟩,x.val.property⟩
  let back (y:↥T) : ↥(Vᶜ:Set ↥(Uᶜ:Set X)) :=
    let v : ↥(Uᶜ:Set X) := ⟨y.val.val,y.property⟩
    ⟨v,fun h => y.val.property ⟨v,h,rfl⟩⟩
  let e : (G.induce Uᶜ).induce Vᶜ ≃g Y.induce T := {
    toEquiv := {toFun := send,invFun := back,left_inv := fun _ => rfl,right_inv := fun _ => rfl}
    map_rel_iff' := fun {v w} => ⟨fun adj => adj.1,fun adj => ⟨adj,fun h => h.2 ⟨v.val.property,w.val.property⟩⟩⟩ }
  apply forcingRow_of_iso e.symm
  intro i j l q ij il jq pl pq
  exact forces_on_incident_labels Y T inside (fun z:Fin l => n (i+z.val)) (fun z:Fin q => m (j+z.val))
    (fun z => pn _ (by have := z.isLt;omega)) (fun z => pm _ (by have := z.isLt;omega))
    (row i j l q ij il jq pl pq)



namespace TenPortSupport
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)

/-- One actual incident piece is assigned to one colour at each new angular
pair. The same set of exterior vertices is erased for the entire row. -/
theorem whole_piece_menu {s t r:ℕ} (n m:ℕ→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i<s,0<n i) (pm:∀i<t,0<m i) (row:ForcingRow G s t n m r)
    (V:Set ↥(W.supportᶜ:Set X)) (fit:W.rank≤r+V.ncard+1) :
    ForcingRow (W.outside.induce Vᶜ) s t n m (r+V.ncard+W.rank) := by
  classical
  let part := fun _:Fin 1 => W.piece
  let z := fun _:Fin 1 => W.rank
  let S : Set X := Subtype.val '' V
  have card : S.ncard=V.ncard := Set.ncard_image_of_injective V Subtype.val_injective
  have small (i:Fin 1) : z i≤r+S.ncard+1 := card.symm ▸ fit
  have total : (∑i,z i)=W.rank := by simp [z]
  have union : Finset.univ.sup part=W.piece := by simp [part]
  have price (T:Finset (Fin 1)) : matchingEdges (T.sup part)≤∑i∈T,z i := subfamily_rank_le_sum part T
  have next := actual_piece_menu_of_splits G S part z n m hn hm pn pm
    (fun _ => eraseInternal_le G _) price (split_capacities_of_small z _ small) row
  rw [union,total,card] at next
  exact incident_exterior_forcing_row G W.support V n m pn pm next

#print axioms whole_piece_menu
end TenPortSupport
#print axioms incident_exterior_forcing_row
end JSP452Audit.StarHost
