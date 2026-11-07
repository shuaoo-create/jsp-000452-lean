import Mathlib.Combinatorics.SimpleGraph.Maps

namespace JSP452Audit.StarHost

open SimpleGraph

variable {X : Type*}

/-- Extend a graph on the surviving vertices, leaving the restored vertex isolated. -/
def extendAway (v : X) (R : SimpleGraph {x : X // x ≠ v}) : SimpleGraph X :=
  R.map (Function.Embedding.subtype (· ≠ v))

@[simp] theorem extendAway_induce (v : X) (R : SimpleGraph {x : X // x ≠ v}) :
    (extendAway v R).induce {x | x ≠ v} = R := by
  ext a b
  exact SimpleGraph.map_adj_apply

theorem extendAway_endpoints {v x y : X} {R : SimpleGraph {z : X // z ≠ v}}
    (h : (extendAway v R).Adj x y) : x ≠ v ∧ y ≠ v := by
  obtain ⟨a, b, _, rfl, rfl⟩ := (SimpleGraph.map_adj _ R x y).mp h
  exact ⟨a.property, b.property⟩

theorem extendAway_le (G : SimpleGraph X) (v : X) (R : SimpleGraph {x : X // x ≠ v})
    (hR : R ≤ G.induce {x | x ≠ v}) : extendAway v R ≤ G :=
  (SimpleGraph.map_le_iff_le_comap _ _ _).mpr hR

/-- Color every incident edge red. Equivalently the only blue edges are the lifted old blue edges. -/
def restoreIncidentRed (G : SimpleGraph X) (v : X) (R : SimpleGraph {x : X // x ≠ v}) :
    SimpleGraph X := G \ extendAway v (G.induce {x | x ≠ v} \ R)

theorem restoreIncidentRed_le (G : SimpleGraph X) (v : X) (R : SimpleGraph {x : X // x ≠ v}) :
    restoreIncidentRed G v R ≤ G := sdiff_le

theorem restoreIncidentRed_incident (G : SimpleGraph X) (v : X)
    (R : SimpleGraph {x : X // x ≠ v}) (x : X) :
    (restoreIncidentRed G v R).Adj v x ↔ G.Adj v x :=
  ⟨And.left, fun h => ⟨h, fun hr => (extendAway_endpoints hr).1 rfl⟩⟩

theorem restoreIncidentRed_blue (G : SimpleGraph X) (v : X)
    (R : SimpleGraph {x : X // x ≠ v}) :
    G \ restoreIncidentRed G v R = extendAway v (G.induce {x | x ≠ v} \ R) :=
  sdiff_sdiff_eq_self (extendAway_le G v _ sdiff_le)

theorem restoreIncidentRed_blue_endpoints {G : SimpleGraph X} {v x y : X}
    {R : SimpleGraph {z : X // z ≠ v}} (h : (G \ restoreIncidentRed G v R).Adj x y) :
    x ≠ v ∧ y ≠ v := by
  rw [restoreIncidentRed_blue] at h
  exact extendAway_endpoints h

/-- Exact restriction on the survivor graph if the input really is a red subgraph. -/
theorem restoreIncidentRed_induce (G : SimpleGraph X) (v : X)
    (R : SimpleGraph {x : X // x ≠ v}) (hR : R ≤ G.induce {x | x ≠ v}) :
    (restoreIncidentRed G v R).induce {x | x ≠ v} = R := by
  have restrict : (restoreIncidentRed G v R).induce {x | x ≠ v} =
      G.induce {x | x ≠ v} \ (extendAway v (G.induce {x | x ≠ v} \ R)).induce {x | x ≠ v} := rfl
  rw [restrict, extendAway_induce, sdiff_sdiff_eq_self hR]

theorem restoreIncidentRed_blue_induce (G : SimpleGraph X) (v : X)
    (R : SimpleGraph {x : X // x ≠ v}) :
    (G \ restoreIncidentRed G v R).induce {x | x ≠ v} = G.induce {x | x ≠ v} \ R := by
  rw [restoreIncidentRed_blue, extendAway_induce]

/-- Interchange the roles of the two colors: extending red away from v makes all
incident edges blue, and the blue graph is the corresponding all-incident-red construction. -/
theorem extendAway_blue_eq_restore (G : SimpleGraph X) (v : X)
    (R : SimpleGraph {x : X // x ≠ v}) (hR : R ≤ G.induce {x | x ≠ v}) :
    G \ extendAway v R = restoreIncidentRed G v (G.induce {x | x ≠ v} \ R) := by
  unfold restoreIncidentRed
  rw [sdiff_sdiff_eq_self hR]

#print axioms extendAway
#print axioms extendAway_induce
#print axioms extendAway_endpoints
#print axioms extendAway_le
#print axioms restoreIncidentRed_le
#print axioms restoreIncidentRed_incident
#print axioms restoreIncidentRed_blue
#print axioms restoreIncidentRed_blue_endpoints
#print axioms restoreIncidentRed_induce
#print axioms restoreIncidentRed_blue_induce
#print axioms extendAway_blue_eq_restore

end JSP452Audit.StarHost
