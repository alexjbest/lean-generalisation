import algebra.group_power
import topology.metric_space.basic
import algebra.ring
import generalise
import meta.expr
import tactic.group
import tactic
import init.data.ordering.basic init.function init.meta.name init.meta.format init.control.monad


-- TODO ensure this works for things with random names distrib_lattice_of_linear_order
-- TODO maybe use the explicit name_map and name_set
-- TODO fanciness like ∀ n : ℕ, n = n ∧ ∀ {R : Type} [ring R], R = R wont generalise but wgaf
-- TODO clean up : shouldn't fire as is_add_hom doesn't take alpha as an arg
-- TODO check type as well, proof could just be rfl gpow_neg_succ_of_nat
-- is_add_hom.id:
--   File: /Users/alex/lean-generalisation/_target/deps/mathlib/src/deprecated/group.lean
--   Line: 65
--   Type: instance
--   Source: has_add
--   Target: is_add_hom
-- same for list.has_insert and finset.has_insert, idem dito list.is_lawful_singleton
open tactic declaration environment native
namespace native
namespace rb_lmap
open rb_map prod format
section
variables {key : Type} {data : Type} [has_to_format key] [has_to_format data]
private meta def format_key_data (k : key) (d : data) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt "id :" ++ to_fmt k ++ space ++ to_fmt ":" ++ space ++ to_fmt d -- todo what symbol?

meta instance : has_to_format (rb_lmap key data) :=
⟨λ m, group $ to_fmt "[" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ k d p, (fst p ++ format_key_data k d (snd p), ff)))) ++
              to_fmt "]"⟩
end
end rb_lmap
end native

section
setup_tactic_parser
namespace interactive
-- should print with pp.all turned on
@[user_command]
meta def allprint (_ : parse $ tk "#allprint") : lean.parser unit :=
do-- l ← pp "a",
  l← parser.pexpr,
  trace l, -- TODO there is a command for this
  return ()
  end interactive
--#allprint native.rb_lmap.format_key_data
end

/- prints information about `decl` if it is an instance or a class. If `print_args` is true, it also prints
  arguments of the class as "instances" (like `topological_monoid -> monoid`). -/
meta def print_item_yaml (env : environment) (print_args : bool) (decl : declaration)
  : tactic unit :=
let name := decl.to_name in
do
    when (env.decl_olean name).is_some $ do
      olean_file ← env.decl_olean name,
      let s:= ":\n  File: " ++ olean_file ++ "\n  Line: " ++
              pos_line (env.decl_pos name),
      tactic.has_attribute `instance name >> (do
            (l, tgt) ← return decl.type.pi_binders,
            guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
            guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
            let src := to_string l.ilast.type.erase_annotations.get_app_fn.const_name,
            let tgt := to_string tgt.erase_annotations.get_app_fn.const_name,
            guard (src ≠ tgt),
            trace $ to_string decl.to_name ++ s,
            trace "  Type: instance",
            trace $ "  Source: " ++ src,
            trace $ "  Target: " ++ tgt) <|>
      tactic.has_attribute `class name >> (do
            (l, tgt) ← return decl.type.pi_binders,
            guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
            trace $ to_string decl.to_name ++ s,
            trace "  Type: class",
            when print_args $ l.tail.mmap' (λ arg, do
              let nm := arg.type.erase_annotations.get_app_fn.const_name.to_string,
              trace $ "arg_of_" ++ decl.to_name.to_string ++ "_" ++ nm ++ s,
              trace "  Type: instance",
              trace $ "  Source: " ++ decl.to_name.to_string,
              trace $ "  Target: " ++ nm)
            ) <|>
      skip

/- class tree. -/
meta def class_tree (env : environment) (print_args : bool) : tactic (native.rb_lmap name name) :=
do t ← env.mfold (native.rb_lmap.mk name name)
  (λ decl a, let name := decl.to_name in do
    tactic.has_attribute `instance name >> (do
      (l, tgt) ← return decl.type.pi_binders,
      guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
      guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
      guard l.head.type.is_sort,
      trace name,
      trace l,
      trace tgt,
      let src := l.ilast.type.erase_annotations.get_app_fn.const_name,
      let tgt := tgt.erase_annotations.get_app_fn.const_name,
      guard (src ≠ tgt),
      return (a.insert src tgt)) <|>
      return a),
  -- trace t,
  return t

meta def print_tree : tactic unit := do c ← get_env, class_tree c tt >>= trace
--run_cmd print_tree
meta def subtree : name → native.rb_lmap name name → native.rb_lmap name name :=
λ n t,
  (t.find n).foldl
  (λ old ins,
    (native.rb_map.fold (subtree ins t) old
      (λ k d a, native.rb_map.insert a k d)).insert n ins)
  (native.rb_lmap.mk name name)

meta def ex : tactic unit :=
do
  let l := (((native.rb_lmap.mk name name).insert `a `b).insert `b `c).insert `a `d,
  trace l,
  trace (l.find `a),
  let k := subtree `a l,
  trace k,
  return ()
-- run_cmd ex

meta def print_subtree (n : name) : tactic unit :=
do
  c ← get_env,
  -- d ← get_decl a,
  t ← class_tree c tt,
  trace (subtree n t),
  return ()
--run_cmd print_subtree `ring
/-- prints information about unary classes and forgetful instances in the environment.
  It only prints instances and classes that have at most 1 argument that is not a type-class argument
  (within square brackets), and the instances can only be forgetful instances (where the conclusion
  is a class applied to a variable) -/
meta def print_content' : tactic unit :=
do curr_env ← get_env,
   (curr_env.fold list.nil list.cons).mmap' (print_item_yaml curr_env tt)

meta def test (n : name) : tactic unit :=
do curr_env ← get_env,
   d ← get_decl n,
   trace (to_string d.to_name),
   print_item_yaml curr_env tt d

--run_cmd test `add_monoid.to_has_zero
--run_cmd print_content'

open tactic declaration environment expr
meta def factors_through (names : list name) (tc : name) : tactic (list name) :=
do
  pots ← names.mfilter (λ n, return (n.components.head = tc)),
  trace ">>>>>>>>>>>>>>",
  trace pots,
  return names

meta def find_gens : expr → ℕ → tactic string
| (lam na binder_info.inst_implicit ty body) (n) := do
  -- trace $ "type " ++ to_string ty,
  -- trace $ "body " ++ to_string body,
  -- trace "n ",
  -- trace n,
  ts ← body.mfold [] (λ ex le ol, do
    guard (ex.is_app && (tt && (ex.app_arg = var le))) >> (do
    -- trace $ get_app_fn ex,
    -- trace ex,
    -- trace le,
    -- trace ex.app_arg,
    return ((get_app_fn ex) :: ol)) <|> return ol),
  if ts.length = 1 then trace ">>> only 1" >> trace ts else skip,
  return "" --$ to_string (na,ty,body) -- instance
| (lam _ _ _ body) (n) := find_gens body (n + 1) -- keep looking
| _ _ := return "nada"

meta def print_gens (env : environment) (decl : declaration) : tactic unit :=
let name := decl.to_name --,
    --pos := pos_line (env.decl_pos name),
    --fname := file_name (env.decl_olean name)
    in
do
  trace ("- Name: " ++ to_string name),
  --trace ("  File: " ++ fname),
  --trace ("  Line: " ++ pos),
  --trace ("  Kind: " ++ decl.get_kind_string),
  --mods ← env.get_modifiers name,
  --trace ("  Modifiers: " ++ to_string mods),
  pp_type ← pp decl.type,
  trace ("  Type: " ++ (to_string pp_type).quote),
  type_proofs ← (list_items decl.type).mfilter $ λ c, mk_const c >>= is_proof,
  type_others ← (list_items decl.type).mfilter $ λ c, mk_const c >>= is_proof >>= mnot,
  trace ("  Type uses proofs: " ++ to_string type_proofs),
  trace ("  Type uses others: " ++ to_string type_others),
  classes_in_type ← (list_items decl.type).mfilter $ λ c, (has_attribute `class c >> return tt) <|> return ff,
  pp_value ← pp decl.value,
  trace ("  Value: " ++ (to_string pp_value).quote),
  --let aa := (list_items decl.value),
 -- trace aa,
  classes_in_val ← (list_items decl.value).mfilter $ λ c, (has_attribute `class c >> return tt) <|> return ff,
  value_others ← (list_items decl.value).mfilter $ λ c, mk_const c >>= is_proof >>= mnot,
    trace (find_gens decl.value 0),
  -- a ← classes_in_type.mmap (λ c,
  -- do
  --   trace "generalising",
  --   trace c,
    -- trace ">>>>>>>>",
    -- (l, tgt) ← return decl.value.pi_binders,
    -- trace l,
    -- trace tgt,
    -- b ← decl.value.mfold tt (λ e n a, do (guard e.is_app >> do trace "---",
    -- trace n,
    -- trace e,
    -- trace e.app_fn,
    -- trace e.app_arg,
    -- trace e.app_arg.is_var,
    -- return ff) <|> return tt),
    -- return b
  --   return ()
  -- ),
  trace ("  classes: " ++ to_string classes_in_val),
  trace ("  Value uses others: " ++ to_string value_others),
  --trace ("  tr: " ++ to_string decl.is_trusted),
  --  trace ("  Target class: " ++ if mods.Instance then to_string decl.type.get_pi_app_fn else ""),
  -- trace ("  Parent: " ++  match env.is_projection name with
  --                         | some info := to_string info.cname
  --                         | none :=  ""
  --                         end),
  trace ("  Fields: " ++ (to_string $ (env.structure_fields_full name).get_or_else []))
-- #print filter.has_antimono_basis.mono
meta def gene : tactic unit :=
do curr_env ← get_env,
  let decls := curr_env.fold [] list.cons,
  let local_decls := decls.filter
    (λ x, --environment.in_current_file curr_env (to_name x) &&
      not (to_name x).is_internal
      && x.is_trusted), -- don't worry about meta stuff?
  local_decls.mmap' (print_gens curr_env)

open expr
section examples
  --set_option pp.all true
  lemma good (G : Type*) [comm_group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end
  -- #print good

  lemma good2 (G : Type*) [add_monoid G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  lemma bad (G : Type*) [group G] (n : ℕ) (g : G) (h : g^n = 1) : g^(2*n) = 1 :=
  by rw [pow_mul', h, one_pow]

  lemma bad2 (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- statement generalises but proof does now
  lemma bad3 (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by simp only [nsmul_eq_mul] at h; simp only [nat.cast_bit0, nsmul_eq_mul, nat.cast_one, nat.cast_mul]; assoc_rewrite h; exact mul_zero 2

  lemma bad4 (G : Type*) [add_comm_group G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  lemma bad5 (G : Type*) [add_group G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  lemma bad6 (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _
  lemma bad8 (G H : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _
  -- TODO looks like some instance missed here? possibly in the pi binder
  -- lemma bad7 (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g ∧ ∀ g2, g2 + g = g + g2 :=
  -- ⟨add_comm _ _,assume g2, add_comm _ _ ⟩

end examples
run_cmd gene
set_option pp.all true
-- #print bad6
meta def aaa :=
do l ← find_ancestors `integral_domain (const `int []),
trace l,
return ()
-- run_cmd aaa
-- #check and.intro
set_option pp.all true
meta def a: tactic unit := do
do let e:= (app (const `add_comm_monoid [level.zero]) (const `nat []) : expr),
tgt ← return e >>= instantiate_mvars,
   b   ← is_class tgt,
   trace tgt,
   trace b,
   if b then mk_instance tgt >>= trace
   else skip,
   return ()
-- run_cmd a
-- #print reset_instance_cache
/-

Pseudocode:
- For each class C in the type, e.g. [ring H] [topological_ring G] (probably called _inst_1):
  - Find occurences of projections from ring.to_add_comm_group C, ring

-/
set_option pp.all true
#check ring.to_add_comm_group
