import tactic
import data.finset.basic
variables (T : Type) [has_lt T] [decidable_rel ((<) : T → T → Prop)]
meta def dag : Type := native.rb_lmap T T

namespace dag

meta def mk : dag T := native.rb_lmap.mk T T
variable {T}
meta def insert_vertex (d : dag T) (a : T) : dag T :=
if ¬ native.rb_map.contains d a then
  native.rb_map.insert d a []
else
  d
meta def insert_vertices (d : dag T) (a : list T) : dag T := a.foldl insert_vertex d
variable [decidable_eq T]
meta def insert_edge (d : dag T) (v w : T) : dag T := if w ∈ d.find v then d else insert_vertex (native.rb_lmap.insert d v w) w
meta def insert_edges (d : dag T) (a : list (T × T)) : dag T := a.foldl (λ da ⟨v, w⟩, insert_edge da v w) d
meta def vertices : dag T → list T := native.rb_map.keys
meta def edges (d : dag T) : list (T × T) := native.rb_map.fold d []
  (λ v es old, old ++ es.map (λ x, (v, x)))
meta def erase_all (d : dag T) (l : list T) : dag T := l.foldl (λ o v, native.rb_map.fold (native.rb_map.erase o v) (native.rb_map.erase o v) (λ w ll oll, native.rb_map.insert oll w (ll.erase v))) d

variables [has_to_format T]
open format prod native.rb_map
private meta def format_key_data (k : T) (d : list T) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt "id :" ++ to_fmt k ++ space ++ to_fmt ":" ++ space ++ to_fmt d -- todo what symbol?

meta instance : has_to_format (dag T) :=
⟨λ m, group $ to_fmt "[" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ k d p, (fst p ++ format_key_data k d (snd p), ff)))) ++
              to_fmt "]"⟩
meta instance : has_repr (dag T) := ⟨λ s, (has_to_format.to_format s).to_string⟩

/-- Take the sub-graph of things reachable from name-/
-- TODO is this inefficient?
meta def reachable : T → dag T → dag T :=
λ n t,
  (t.find n).foldl
  (λ old ins,
    (native.rb_map.fold (reachable ins t) old
      (λ k d a, native.rb_map.insert a k d)).insert n ins)
  (dag.mk T)
/- Take the sub-graph of things reachable from a list of names-/
-- meta def reachable'_core (orig : dag T) : list T → native.rb_map T bool → dag T → dag T
-- | (h :: l) vis d := (orig.find h).foldl (λ o w, reachable'_core l vis d) (vis.insert h tt)
-- | [] _ d := d
-- meta def reachable' : list T → dag T → dag T :=
-- λ l d, reachable'_core l
  -- (d.fold (native.rb_map.mk _ _) (λ v _ o, o.insert v false)) d
-- λ n t,
--   (t.find n).foldl
--   (λ old ins,
--     (native.rb_map.fold (reachable ins t) old
--       (λ k d a, native.rb_map.insert a k d)).insert n ins)
--   (dag.mk T)

/-- Depth first search used for topological sorting. -/
meta def dfs (d : dag T) : T → list T → native.rb_map T bool → (list T × native.rb_map T bool)
| v stack visited :=
  (λ a : list T × native.rb_map T bool, (v :: a.fst, a.snd))
    ((d.find v).foldl
      (λ ⟨sta, vis⟩ w,
        if (vis.find w).get_or_else ff then
          (sta, vis)
        else
          dfs w sta vis)
      (stack, visited.insert v tt))
-- #eval (((((dag.mk ℕ).insert_vertex 3).insert_edge 2 1).insert_edge 2 3).dfs 2 [] (native.rb_map.mk _ _)).fst
meta def minimal_vertices_dfs (d : dag T) : T → native.rb_map T bool → native.rb_map T bool → (native.rb_map T bool × native.rb_map T bool)
| v minimals visited :=
  -- (λ a : native.rb_map T bool × native.rb_map T bool, (a.fst.insert, a.snd))
    ((d.find v).foldl
      (λ ⟨mins, vis⟩ w,
        if (vis.find w).get_or_else ff then
          (mins.insert w ff, vis)
        else
          minimal_vertices_dfs w (mins.insert w ff) vis)
      (minimals, visited.insert v tt))
-- #eval to_string (((((dag.mk ℕ).insert_vertex 3).insert_edge 2 1).insert_edge 2 3).minimal_vertices_dfs 1 (native.rb_map.mk _ _) (native.rb_map.mk _ _)).fst
open native.rb_set
/-- Return the list of minimal vertices in a dag -/
meta def minimal_vertices (d : dag T) (start : native.rb_set T) : native.rb_set T :=
  native.rb_map.fold
  (start.fold
    ((d.vertices.foldl (λ ol t, native.rb_map.insert ol t tt) (native.rb_map.mk T bool),
      d.vertices.foldl (λ ol t, native.rb_map.insert ol t ff) (native.rb_map.mk T bool)) :
      native.rb_map T bool × native.rb_map T bool)
    (λ (v : T) (minsvis : native.rb_map T bool × native.rb_map T bool),
      if (minsvis.2.find v).get_or_else ff then
        minsvis
      else
        minimal_vertices_dfs d v minsvis.1 minsvis.2)
  ).fst (native.rb_map.mk _ _) (λ w b ol, if b && start.contains w then ol.insert w else ol)
-- #eval (((dag.mk ℕ).insert_vertex 3).insert_edges [(2, 1), (2, 3), (4,2)]).minimal_vertices [1,2]


/-- Return a topological sort of the DAG. -/
meta def topological_sort (d : dag T) : list T :=
  (native.rb_map.fold d
    (([] : list T), d.vertices.foldl (λ ol t, native.rb_map.insert ol t ff) (native.rb_map.mk T bool))
    (λ v es ⟨stack, vis⟩,
      if (vis.find v).get_or_else ff then
        ⟨stack, vis⟩
      else
        dfs d v stack vis)
  ).fst
-- meta def topological_sort' (d : dag T) [has_to_string T]:tactic unit :=
-- do
--   native.rb_map.mfold d
--     (([] : list T), d.vertices.foldl (λ ol t, native.rb_map.insert ol t ff) (native.rb_map.mk T bool))
--     (λ v es ⟨stack, vis⟩,
--       if (vis.find v).get_or_else ff then
--         do
--         tactic.trace "a",
--         tactic.trace $ to_string v,
--         tactic.trace $ to_string stack,
--         tactic.trace $ to_string vis,
--         return ⟨stack, vis⟩
--       else
--         do
--         tactic.trace "b",
--         tactic.trace $ to_string v,
--         return $ dfs d v stack vis),
--     return ()
-- #eval (λ d : dag _, (d.dfs 5 ([] : list _) (d.vertices.foldl (λ ol t, native.rb_map.insert ol t ff) (native.rb_map.mk _ bool))).fst) (((dag.mk ℕ).insert_vertices [0, 1, 2, 3, 4, 5]).insert_edges [(5, 2), (5,0),(4,0),(4,1),(2,3),(3,1)])
-- #eval (((dag.mk ℕ).insert_vertices [0, 1, 2]).insert_edges [(0, 1), (2,1),(0,2)])
-- run_cmd (((dag.mk ℕ).insert_vertices [0, 1, 2]).insert_edges [(0, 1), (2,1),(0,2)]).topological_sort'

-- [id :linear_ordered_add_comm_group : [linear_ordered_cancel_add_comm_monoid, linear_order],
--  id :linear_order : [],
--  id :linear_ordered_cancel_add_comm_monoid : [linear_order]]

end dag
