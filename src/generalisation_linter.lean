import algebra.group_power
import dag
import topology.metric_space.basic
import algebra.ring
import generalise
import meta.expr
import tactic.group
import tactic
import algebra.char_p
import algebra.category.Group
import init.data.ordering.basic init.function init.meta.name init.meta.format init.control.monad
import meta.rb_map
--import all


declare_trace generalising
open native
set_option trace.generalising false
/-- A shorthand for tracing when the `trace.generalising` option is set to true. -/
meta def generalising_trace {α} [has_to_tactic_format α] (s : α) : tactic unit :=
tactic.when_tracing `generalising (tactic.trace s)

-- TODO better output (include variable names? copy pastable?)
-- TODO better error messages and better tracing
-- TODO dont pass env around as much
-- TODO clean up for graphs : shouldn't fire as is_add_hom doesn't take alpha as an arg
-- including some autogenerated would be good _proof_ for instances, when all of them match should be reported
-- is_add_hom.id:
--   File: /Users/alex/lean-generalisation/_target/deps/mathlib/src/deprecated/group.lean
--   Line: 65
--   Type: instance
--   Source: has_add
--   Target: is_add_hom
-- same for list.has_insert and finset.has_insert, idem dito list.is_lawful_singleton
-- TODO whats up with  filter.tendsto_Ixx_class same as above?
-- TODO list.mem_of_mem_inter_right looks like it needs two eta reductions?
-- TODO why didn't we find sub_le_of_abs_sub_le_left linear_ordered_ring -> linear_ordered_add_comm_group
-- TODO bundled algebraic_geometry.LocallyRingedSpace.to_SheafedSpace algebraic_geometry.LocallyRingedSpace.forget_to_SheafedSpace
-- TODO remove with_top.add_top order_dual.blah opposite.blah
-- TODO fanciness like ∀ n : ℕ, n = n ∧ ∀ {R : Type} [ring R], R = R wont generalise but wgaf
-- TODO check if infinite.nonempty ever applies , its a lemma now
-- TODO maybe use the explicit name_map and name_set
-- TODO look at fintype.decidable_surjective_fintype here the inst is inside  a lambda
-- TODO linter for too many typeclasses in
  -- section
  -- open filter

  -- open set
  -- variables {α : Type} {β : Type} {γ : Type} {ι : Type} {ι' : Type} {l' : filter α} {t : set α} {i : ι} {p' : ι' → Prop} {s' : ι' → set α} {i' : ι'} (l : filter α) (p : ι → Prop) (s : ι → set α) [preorder ι]
  -- structure has_antimono_basis' [preorder ι] (l : filter α) (p : ι → Prop) (s : ι → set α)
  --   extends has_basis l p s : Prop :=
  -- (decreasing : ∀ {i j}, p i → p j → i ≤ j → s j ⊆ s i)
  -- (mono : monotone p)
  -- #print has_antimono_basis'
  -- end

-- Doing:

-- Done:
-- why are we only finding one of ring_hom.char_p_iff_char_p
-- this reveals an interesting diamond it seems
-- field --------> division_ring
--      \                       \
--       v                       v
--     euclidean_domain -> nontrivial
-- why does actual inhabited linter not find Cauchy_eq - it only looks for nondep but in this case Lim depends on it
-- false positive for no args equiv.set.sum_diff_subset_apply_inr as use of inst wrapped in a lambda
--  false pos linear_ordered_field.mul_one
-- category_theory.category.comp_id contains a macro so shouldnt be returned
-- check fpow_zero probably another rfl ting
-- check type as well, proof could just be rfl gpow_neg_succ_of_nat
-- all the rfl ones maybe @rfl (blah) shouldn't blah or type of blah contain the tc  to_topological_space_prod prod.inv_mk
-- subtype.mk_le_mk is also making use of defeq so it looks like inst doesnt really appear in the body, this should also be fixed by cheking the type as well as value
-- ensure this works for things with random names distrib_lattice_of_linear_order
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

set_option trace.generalising false
/- class tree. -/
meta def class_dag (env : environment) : tactic (dag name) :=
do t ← env.mfold (dag.mk name)
  (λ decl a, let name := decl.to_name in do
    tactic.has_attribute `instance name >> (do
      (l, tgt) ← return decl.type.pi_binders,
      -- guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
      guard (l.tail.all $ λ b, (b.info = binder_info.inst_implicit) || (b.info = binder_info.implicit)),
      guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
      guard l.head.type.is_sort,
      -- generalising_trace name,
      -- generalising_trace l,
      -- generalising_trace tgt,
      let src := l.ilast.type.erase_annotations.get_app_fn.const_name,
      let tgt := tgt.erase_annotations.get_app_fn.const_name,
      guard (src ≠ tgt),
      return (a.insert_edge src tgt)) <|>
      return a),
  -- generalising_trace t,
  return t

set_option pp.all true
-- TODO
    -- #check mul_action.to_has_scalar -- want this
    -- #check ring_hom.has_coe_to_fun -- not this
    set_option trace.generalising true
  -- run_cmd do decl ← get_decl `mul_action.to_has_scalar,
    -- let name := decl.to_name in do
    -- tactic.has_attribute `instance name >> (do
    --   (l, tgt) ← return decl.type.pi_binders,
    --   guard (l.tail.all $ λ b, (b.info = binder_info.inst_implicit) || (b.info = binder_info.implicit)),
    --   guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
    --   guard l.head.type.is_sort,
    --   generalising_trace name,
    --   generalising_trace l,
    --   generalising_trace tgt,
    --   let src := l.ilast.type.erase_annotations.get_app_fn.const_name,
    --   let tgt := tgt.erase_annotations.get_app_fn.const_name,
    --   guard (src ≠ tgt),
    --   trace ((dag.mk _root_.name).insert_edge src tgt)) <|>
    --   trace (dag.mk _root_.name)

meta def print_dag : tactic unit := do c ← get_env, class_dag c >>= trace
-- run_cmd print_dag
meta def print_div (l : list name) : tactic unit :=
do c ← get_env,
  class_dag c >>= (λ d, trace $ d.minimal_vertices (native.rb_set.of_list l))
    --`division_ring, `nontrivial, `has_one])
-- run_cmd print_div [ `linear_order, `linear_ordered_add_comm_group, `ordered_ring ]
-- run_cmd print_div [ `has_add, `has_zero, `add_monoid, `has_zero, `has_add,`add_monoid ]

open dag

meta def print_reachable (n : name) : tactic unit :=
do
  c ← get_env,
  -- d ← get_decl a,
  t ← class_dag c,
  trace (reachable n t),
  return ()
meta def print_tos_reachable (n : name) : tactic unit :=
do
  c ← get_env,
  -- d ← get_decl a,
  t ← class_dag c,
  trace $ topological_sort (reachable n t),
--   let r := erase_all (reachable n t) [`preorder, `is_well_order, `t0_space, `t1_space,
-- `is_well_order, `lattice, `is_strict_weak_order, `is_idempotent, `is_total_preorder, `is_linear_order, `is_strict_total_order', `is_incomp_trans, `is_total, `is_total_preorder, `directed_order, `distrib_lattice, `lattice, `semilattice_inf, `has_inf, `semilattice_sup, `filter.ne_bot, `has_sup, `is_idempotent, `is_order_connected, `is_trichotomous, `is_strict_total_order, `ordered_ring, `ordered_add_comm_group, `ordered_semiring, `ordered_cancel_add_comm_monoid, `partial_order, `ordered_add_comm_monoid, `partial_order, `is_partial_order, `preorder, `is_antisymm, `ring, `add_comm_group, `add_group, `has_neg, `has_sub, `add_subgroup.normal,
-- `add_cancel_monoid, `add_cancel_comm_monoid, `add_right_cancel_comm_monoid, `is_add_group_hom, `monoid, `semiring, `semimodule, `monoid_with_zero, `mul_zero_class, `monoid, `has_dvd, `has_one, `has_pow, `semigroup, `is_monoid_hom, `distrib, `has_mul, `is_mul_hom, `add_left_cancel_comm_monoid, `add_left_cancel_monoid,
-- `add_left_cancel_semigroup, -- `add_comm_monoid, -- `add_comm_semigroup, -- `is_commutative, -- `add_right_cancel_monoid, -- `add_right_cancel_semigroup, -- `add_semigroup, -- `add_monoid, -- `is_right_id, -- `is_left_id, -- `has_zero, -- `domain, -- `decidable_eq, -- `has_add, -- `linear_ordered_ring, -- `nonempty, -- `no_top_order,
-- `no_bot_order, -- `discrete_topology, -- `cancel_monoid_with_zero, -- `char_zero, -- `char_p, -- `ordered_semiring, -- `char_zero, -- `subsingleton, -- `discrete_topology, -- `decidable_eq, -- `infinite, -- `ordered_semiring, -- `linear_ordered_semiring, -- `char_zero, -- `t2_space,
-- `t1_space, -- `totally_separated_space, -- `totally_disconnected_space, -- `nontrivial, -- `nonempty, -- `no_bot_order, -- `no_top_order
--   ],
--   r.mfold () (λ a o oo, do trace (to_bool ( `linear_order ∈ o)), return ()),
  return ()
-- run_cmd print_reachable `linear_ordered_ring
-- run_cmd print_tos_reachable `linear_ordered_ring
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
   generalising_trace (to_string d.to_name),
   print_item_yaml curr_env tt d

--run_cmd test `add_monoid.to_has_zero
--run_cmd print_content'

open tactic declaration environment expr
-- a really silly early attempt?
meta def factors_through (names : list name) (tc : name) : tactic (list name) :=
do
  pots ← names.mfilter (λ n, return (n.components.head = tc)),
  generalising_trace ">>>>>>>>>>>>>>",
  generalising_trace pots,
  return names

-- These types are banned as they look like they could be generalisations, i.e. why
-- assume `has_add α` when all you need is `has_add (order_dual α)`, but in these cases
-- the classes are equivalent, likewise with prod we have addition on the prod iff addition
-- on each component so we do not gain anything by removing these.
def banned_aliases : list name := [`order_dual, `multiplicative, `additive, `prod]

set_option pp.all true
meta def is_instance_chain : ℕ → expr → tactic bool := λ n e, do
  (do
    guardb e.is_app,
    tactic.has_attribute `instance e.get_app_fn.const_name,
    l ← e.get_app_args.mfoldl (λ ol arg, (&& ol) <$> (tactic.head_eta arg >>= is_instance_chain n)) tt,
    return l)
  <|> (do
    m ← e.match_var,
    --guardb (n ≤ m), -- TODO this might be excessive if later tcs also used
    return tt) <|> (do
  return ff)
  set_option trace.generalising false

-- set_option profiler true
meta def target (cla : name) (t : expr) (n : ℕ) : tactic name :=
do e ← get_env,
  generalising_trace "tgt",
  generalising_trace t,
  (do m ← t.match_var,
    guardb (n = m),
    return cla) <|> (do
  t ← e.get t.get_app_fn.const_name,
  (l, tgt) ← return t.type.pi_binders,
  generalising_trace l,
  generalising_trace tgt,
  -- guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
  -- guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
  let src := to_string l.ilast.type.erase_annotations.get_app_fn.const_name,
  let tgt := to_string tgt.erase_annotations.get_app_fn.const_name,
  return tgt)

open native.rb_set
-- meta def trace_and_return (ss:string){X : Type*} [has_to_format X] (x : tactic X): tactic X := do l ←  x, trace ("out"++ss), trace l, return l
meta def get_instance_chains (cla : name) : ℕ → expr → tactic (native.rb_set name)
:= λ n e, do
  -- generalising_trace $ "considering " ++ to_string e ++ " " ++ to_string n,
  boo ← is_instance_chain n e,
  if boo then
    (do
      generalising_trace $ "inst chain",
      guardb $ e.has_var_idx n, -- does the chain contain the instance we are generalising?
      generalising_trace $ "contains " ++ to_string n,
      tar ← target cla e n,
      return $ mk_rb_set.insert tar) <|> return mk_rb_set
  else
    match e with
    | (app a a_1)                     := union <$> get_instance_chains n a
                                               <*> get_instance_chains n a_1
    | (lam var_name bi var_type body) := union <$> get_instance_chains n var_type
                                               <*> get_instance_chains (n + 1) body
    | (pi var_name bi var_type body)  := union <$> get_instance_chains n var_type
                                               <*> get_instance_chains (n + 1) body
    | (elet var_name type assi body)  := union <$> (union <$> get_instance_chains n type
                                                          <*> get_instance_chains (n + 1) body)
                                               <*> get_instance_chains n assi
    | (const a a_1) := return mk_rb_set
    | (var a) := return mk_rb_set
    | (sort a) := return mk_rb_set
    | (mvar unique pretty type) := return mk_rb_set
    | (local_const unique pretty bi type) := return mk_rb_set
    | (macro a el) := el.mfoldl (λ ol ex, ol.union <$> get_instance_chains n ex) mk_rb_set
    end
universes u v w
set_option pp.all true
lemma mem_orbit_self
{α : Type u} {β : Type v} [monoid α] [mul_action α β]
(b : β) : b ∈ mul_action.orbit α b :=
⟨1, mul_action.one_smul _⟩
--     #print mem_orbit_self
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mem_orbit_self,trace l.value.binding_body.binding_body.binding_body.binding_body
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mem_orbit_self, aa ← get_instance_chains `mul_action 0 l.value.binding_body.binding_body.binding_body.binding_body , trace $ cd.minimal_vertices aa --.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""
--   run_cmd print_div [`has_scalar,`mul_action]
--   run_cmd print_reachable `has_scalar
--   run_cmd print_reachable `mul_action
--   run_cmd print_dag

lemma aa2 (G : Type) [add_comm_semigroup G] (x : G) : G := x + x

-- run_cmd do e ← get_env, l← e.get `aa2, trace l.value
-- run_cmd do e ← get_env, l← e.get `aa2, l.value.mfold () (λ a b c, do is_instance_chain b a >>= guardb >> trace a <|> skip)
-- run_cmd do e ← get_env, l← e.get `aa2, let a := l.value.lambda_body.app_fn.app_fn.app_arg,trace a, trace $ get_instance_chains `add_comm_semigroup 1 a (pure mk_rb_set)
-- run_cmd do e ← get_env, l← e.get `aa2, let a := l.value.lambda_body.app_fn.app_fn.app_arg.get_app_fn.const_name,
--              trace a,
--             t← e.get a, trace t,
--             (l, tgt) ← return t.type.pi_binders,
--             trace l,
--             trace tgt,
--             -- guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
--             -- guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
--             let src := to_string l.ilast.type.erase_annotations.get_app_fn.const_name,
--             let tgt := to_string tgt.erase_annotations.get_app_fn.const_name,
--             trace tgt
-- #print aa2
-- run_cmd do e ← get_env, l← e.get `aa2, trace $ l.value.lambda_body.app_fn.app_fn
-- run_cmd do e ← get_env, l← e.get `aa2, trace $ is_instance_chain 1 l.value.lambda_body.app_fn.app_fn.app_fn.app_arg
-- run_cmd do e ← get_env, l← e.get `aa2, trace $ get_instance_chains `add_comm_semigroup 1 l.value.lambda_body (pure mk_rb_set)
-- run_cmd do trace $ get_instance_chains `add_comm_monoid 0 `(λ (x : nat), @aa2 _ (@add_comm_monoid.to_add_comm_semigroup _ %%(var 0)) x = x + x) (return mk_rb_set)
-- find the typeclass generalisations possible in a given decl, using old method
-- input should be the type and then the body
-- meta def find_gens (env : environment) : expr → expr → ℕ → string → tactic (option string)
-- -- we match the binders on the type and body simultaneously
-- | (pi tna binder_info.inst_implicit tty tbody) (lam na binder_info.inst_implicit ty body) (n) (s) := do
--   -- We are now trying to generalise `tna` which is of type `tty`
--   generalising_trace $ "type-type " ++ to_string tty,
--   generalising_trace $ "type " ++ to_string ty,
--   if tty ≠ ty then trace "WARNING types not equal" else skip,
--   -- generalising_trace $ "body " ++ to_string body,
--   -- generalising_trace "n ",
--   -- generalising_trace n,
--   -- acc is the main logic, that will be folded over the type and the body
--   let acc : expr → ℕ → list expr × bool → tactic (list expr × bool) := (λ ex le ⟨ol, us⟩, do
--     --if 1 < ol.length then return ⟨ol, us⟩ else do -- TODO for basic algo can fail early if more than one, this didn't seem to make much diference though
--       let us' := us || match ex with  -- is ty the same as a macro name used, this happens when we hit a built in projection
--       | (macro d arg) := ty.get_app_fn.const_name.is_prefix_of $ expr.macro_def_name d
--       | _ := ff
--       end,
--       generalising_trace "ex",
--       generalising_trace ex,
--       l ← head_eta ex.app_arg, -- eta reduce as sometimes there are instances of the form `λ a b, _inst a b`
--       let us'' := us',-- || (l.get_app_fn = var le),
--       guard (ex.is_app && (tt && (l.get_app_fn = var le))) >> -- l.app_fun sometimes the instance used is itself a Pi type and only appears in applied form e.g. pi_Ioc_mem_nhds
--       (do
--         generalising_trace $ get_app_fn ex,
--         generalising_trace le,
--         -- generalising_trace ex.app_arg,
--         guard $ get_app_fn ex ∉ ol,
--         return (get_app_fn ex :: ol, us''))
--       <|> return (ol, us'')),
--   ⟨ts, us⟩ ← body.mfold ([], ff) acc,
--   ⟨ts', us'⟩ ← tbody.mfold (ts, us) acc,
--   generalising_trace ts',
--      --(env.is_projection ex.get_app_fn.const_name >>= λ o, ol),
--   guard ((ts'.length = 0) && (¬us')) >>
--     (find_gens tbody body (n + 1) (s ++ "unused_arg ? " ++ "\n" ++ ty.to_string ++ "\n" ++ ts'.to_string ++ "\n" ++ na.to_string)) <|>
--   guard ((ts'.length = 1) && (¬us') && (ts'.head.get_app_fn.const_name.get_prefix ∉ banned_aliases)) >>
--     (has_attribute `instance ts'.head.const_name >>
--   find_gens tbody body (n + 1) (s ++ "only 1\n" ++ ty.to_string ++ "\n" ++ ts'.to_string ++ "\n" ++ na.to_string)) <|>
--   find_gens tbody body (n + 1) s
--   --$ to_string (na,ty,body) -- instance
-- -- keep looking
-- | (pi _ _ _ tbody) (lam _ _ _ body) n s := find_gens tbody body (n + 1) s
-- | _ _ _ s := if s.length = 0 then return none else return s

-- find the typeclass generalisations possible in a given decl
-- input should be the type and then the body
-- TODO env not needed?
meta def find_gens' (cd : dag name) (env : environment) : expr → expr → ℕ → string → tactic (option string)
-- we match the binders on the type and body simultaneously
| (pi tna binder_info.inst_implicit tty tbody) (lam na binder_info.inst_implicit ty body) n s := do
  -- We are now trying to generalise `tna` which is of type `tty`
  generalising_trace $ "type-type " ++ to_string tty,
  generalising_trace $ "type " ++ to_string ty,
  if tty ≠ ty then trace "WARNING types not equal" else skip,
  (do guard tty.get_app_fn.is_constant, -- for now we ignore things like [∀ i, decidable_eq $ f i]
    -- generalising_trace $ "body " ++ to_string body,
    -- generalising_trace "n ",
    -- generalising_trace n,
    ou  ← get_instance_chains tty.get_app_fn.const_name 0 body,
    tou ← get_instance_chains tty.get_app_fn.const_name 0 tbody,
    generalising_trace ou,
    generalising_trace tou,
    let ans := (λ u, (cd.minimal_vertices u).union $ u.filter (λ v, ¬ cd.contains v)) (ou.union tou),
    generalising_trace ans,
    -- do unused separety
    --  guard ((ans.size = 0) && (¬us')) >>
    --    (find_gens' tbody body (n + 1) (s ++ "unused_arg ? " ++ "\n" ++ ty.to_string ++ "\n" ++ ts'.to_string ++ "\n" ++ na.to_string)) <|>
    -- guard ((ts'.length = 0) && (¬us')) >>
    --   (find_gens' tbody body (n + 1) (s ++ "unused_arg ? " ++ "\n" ++ ty.to_string ++ "\n" ++ ts'.to_string ++ "\n" ++ na.to_string)) <|>
    guard (¬ ans.contains tty.get_app_fn.const_name),
    --  && (¬us')
    generalising_trace ans,
    guard (tty.get_app_fn.const_name.get_prefix ∉ banned_aliases),
    generalising_trace ans,
    --  has_attribute `instance ts'.head.const_name >>
    find_gens' tbody body (n + 1) (s ++ na.to_string ++ ": " ++ ty.get_app_fn.const_name.to_string ++ " ↝" ++ ans.fold "" (λ n ol, ol ++ " " ++ n.to_string) ++ "\n")) <|>
  find_gens' tbody body (n + 1) s
  -- acc is the main logic, that will be folded over the type and the body
  -- let acc : expr → ℕ → list expr × bool → tactic (list expr × bool) := (λ ex le ⟨ol, us⟩, do
  --   --if 1 < ol.length then return ⟨ol, us⟩ else do -- TODO for basic algo can fail early if more than one, this didn't seem to make much diference though
  --     let us' := us || match ex with  -- is ty the same as a macro name used, this happens when we hit a built in projection
  --     | (macro d arg) := ty.get_app_fn.const_name.is_prefix_of $ expr.macro_def_name d
  --     | _ := ff
  --     end,
  --     generalising_trace "ex",
  --     generalising_trace ex,
  --     l ← head_eta ex.app_arg, -- eta reduce as sometimes there are instances of the form `λ a b, _inst a b`
  --     let us'' := us',-- || (l.get_app_fn = var le),
  --     guard (ex.is_app && (tt && (l.get_app_fn = var le))) >> -- l.app_fun sometimes the instance used is itself a Pi type and only appears in applied form e.g. pi_Ioc_mem_nhds
  --     (do
  --       generalising_trace $ get_app_fn ex,
  --       generalising_trace le,
  --       -- generalising_trace ex.app_arg,
  --       guard $ get_app_fn ex ∉ ol,
  --       return (get_app_fn ex :: ol, us''))
  --     <|> return (ol, us'')),
  -- ⟨ts, us⟩ ← body.mfold ([], ff) acc,
  -- ⟨ts', us'⟩ ← tbody.mfold (ts, us) acc,
  -- generalising_trace ts',
     --(env.is_projection ex.get_app_fn.const_name >>= λ o, ol),
  --$ to_string (na,ty,body) -- instance
-- keep looking
| (pi _ _ _ tbody) (lam _ _ _ body) n s := find_gens' tbody body (n + 1) s -- a non instance binder
| _ _ _ s := return (if s.length = 0 then none else s) -- done with binders so finish

-- A mostly useless wrapping class that gets a bunch of debug info and calls find_gens'
meta def print_gens (cd : dag name) (decl : declaration) : tactic (option string) :=
  guard decl.is_trusted >> (do -- ignore meta stuff
  env ← get_env,
  let name := decl.to_name,
  --pos := pos_line (env.decl_pos name),
  let fname := file_name (env.decl_olean name),
  generalising_trace ("- " ++ to_string name ++ " is a " ++ decl.get_kind_string ++ " in " ++ fname),
  --generalising_trace ("  Line: " ++ pos),
  -- generalising_trace ("  Kind: " ++ decl.get_kind_string),
  --mods ← env.get_modifiers name,
  --generalising_trace ("  Modifiers: " ++ to_string mods),
  pp_type ← pp decl.type,
  generalising_trace ("  Type: " ++ (to_string pp_type).quote),
  type_proofs ← (list_items decl.type).mfilter $ λ c, mk_const c >>= is_proof,
  type_others ← (list_items decl.type).mfilter $ λ c, mk_const c >>= is_proof >>= mnot,
  generalising_trace ("  Type uses proofs: " ++ to_string type_proofs),
  generalising_trace ("  Type uses others: " ++ to_string type_others),
  classes_in_type ← (list_items decl.type).mfilter $ λ c, (has_attribute `class c >> return tt) <|> return ff,
  pp_value ← pp decl.value,
  generalising_trace ("  Value: " ++ (to_string pp_value).quote),
  --let aa := (list_items decl.value),
 -- generalising_trace aa,
  classes_in_val ← (list_items decl.value).mfilter $ λ c, (has_attribute `class c >> return tt) <|> return ff,
  value_others ← (list_items decl.value).mfilter $ λ c, mk_const c >>= is_proof >>= mnot,
  generalising_trace ("  classes: " ++ to_string classes_in_val),
  generalising_trace ("  Value uses others: " ++ to_string value_others),
  generalising_trace ("  Fields: " ++ (to_string $ (env.structure_fields_full name).get_or_else [])),
  find_gens' cd env decl.type decl.value 0 ""
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
  --trace ("  tr: " ++ to_string decl.is_trusted),
  --  trace ("  Target class: " ++ if mods.Instance then to_string decl.type.get_pi_app_fn else ""),
  -- trace ("  Parent: " ++  match env.is_projection name with
  --                         | some info := to_string info.cname
  --                         | none :=  ""
  --                         end),
  ) <|> return none

@[user_attribute]
meta def dag_attr : user_attribute (dag name) unit := {
  name := "_dag",
  descr := "(interal) attribute just to store the class dag",
  cache_cfg := ⟨λ _, (do e ← get_env, class_dag e), []⟩
}

meta def print_gens_wrap (decl : declaration) : tactic (option string) :=
do
  e ← get_env,
  cd ← dag_attr.get_cache,
  --  cd ← class_dag e,
  print_gens cd decl

meta def gene : tactic unit := -- old function for running the linter before it was hooked up as a linter
do curr_env ← get_env,
  let decls := curr_env.fold [] list.cons,
  let local_decls := decls.filter
    (λ x, (environment.in_current_file curr_env (to_name x)) &&
      (not (to_name x).is_internal)
      && x.is_trusted), -- don't worry about meta stuff?
  cd ← class_dag curr_env,
  local_decls.mmap' (λ a, (do l ← print_gens cd a, ll ← l, trace a.to_name, trace ll) <|> skip)
--  #print star_injective
section examples
  lemma good (G : Type*) [group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end

  lemma good2 (G : Type*) [add_monoid G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- monoid?
  lemma bad (G : Type*) [group G] (n : ℕ) (g : G) (h : g^n = 1) : g^(2*n) = 1 :=
  by rw [pow_mul', h, one_pow]

  -- harder example as we have a diamond ?
  -- #check ring.to_distrib
  -- #check ring.to_semiring
  -- add_monoid
  lemma bad2diamond (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- statement generalises but proof does not!! this one is hard then
  -- add_monoid linter only finds semiring
  lemma bad3pfbad (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by simp only [nsmul_eq_mul] at h; simp only [nat.cast_bit0, nsmul_eq_mul, nat.cast_one, nat.cast_mul]; assoc_rewrite h; exact mul_zero 2
  set_option pp.all true
  lemma bad3pfbad' (G : Type*) [ring G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by {rw [nsmul_eq_mul] at ⊢ h,  rw [nat.cast_mul, mul_assoc, h], exact mul_zero _}
set_option pp.max_steps 30000
set_option pp.max_depth 30000
set_option pp.goal.max_hypotheses 10000
-- #print bad3pfbad'
-- set_option trace.generalising true
-- run_cmd do d ← get_decl `bad3pfbad',
--   cd ← dag_attr.get_cache,
--   e ← get_env,
--   trace $ find_gens' cd e d.type d.value 0 "",
  -- return ()

  -- add_monoid
  lemma bad4 (G : Type*) [add_comm_group G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- add_monoid
  lemma bad5 (G : Type*) [add_group G] (n : ℕ) (g : G) (h : n •ℕ g = 0) : (2*n)•ℕ g = 0 :=
  by rw [mul_nsmul, h, nsmul_zero]

  -- this works without the second stage checking the body, but it has a diamond if we include the type
  -- add_comm_semigroup
  lemma bad6 (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _
  -- add_comm_semigroup
  lemma bad8 (G H : Type*) [add_comm_group G] (g h : G) : g + h = h + g := add_comm _ _

  -- TODO looks like some instance missed here with original version? possibly in the pi binder
  -- add_comm_semigroup
  lemma bad7pibinder (G : Type*) [add_comm_group G] (g h : G) : g + h = h + g ∧ ∀ g2, g2 + g = g + g2 :=
  ⟨add_comm _ _,assume g2, add_comm _ _ ⟩
  -- challenging example this is a projection but not an instance
  lemma bad10 (G H : Type*) [has_mul G] [has_mul H] [fintype G] [fintype H] (h : G ≃* H) :
  fintype.card G = fintype.card H := fintype.card_congr h.to_equiv
  -- multiple tings
  -- monoid H, fintypes not needed
  lemma bad9 (G H : Type*) [monoid G] [group H] [fintype G] [fintype H] : (1^2 : G) = 1 ∧ (1^2 : H) = 1 :=
  ⟨one_pow 2, one_pow 2⟩

  -- group
  lemma bad11 (G : Type*) [comm_group G] (n : ℤ) (g : G) (h : g^(-n) = 1) : g^n = 1 :=
  begin
    rw [gpow_neg, inv_eq_one] at h,
    exact h,
  end
  -- set_option old_structure_cmd true
-- @[protect_proj] class linear_ordered_field' (α : Type*) extends linear_ordered_comm_ring α, field α
  lemma bun (G: Group) (g :G) : g^2*g^2 = g^4 :=
  begin
    group,
  end

open equiv.set equiv sum nat function set subtype

@[simp] lemma sum_diff_subset_apply_inr' {α : Sort} {β : Sort} {γ : Sort}
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred s] (x : t \ s) :
  equiv.set.sum_diff_subset h (sum.inr x) = inclusion (diff_subset t s) x := rfl
  set_option pp.all false
  -- #check equiv.set.sum_diff_subset
  set_option pp.all true
  -- #print sum_diff_subset_apply_inr'

lemma supr_apply' {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Sup (β i)] {f : ι → Πa, β a}
  {a : α} :
  (⨆i, f i) a = (⨆i, f i a) :=
@infi_apply α (λ i, order_dual (β i)) _ _ f a



variables {α β γ :Type} {ι : Sort} {s : set α}
--none
theorem exists_nat_ge' [linear_ordered_semiring α] [archimedean α] (x : α) :
  ∃ n : ℕ, x ≤ n :=
(exists_nat_gt x).imp $ λ n, le_of_lt

theorem finset_le {r : α → α → Prop} [is_trans α r]
  {ι} [hι : nonempty ι] {f : ι → α} (D : directed r f) (s : finset ι) :
  ∃ z, ∀ i ∈ s, r (f i) (f z) :=
show ∃ z, ∀ i ∈ s.1, r (f i) (f z), from
multiset.induction_on s.1 (let ⟨z⟩ := hι in ⟨z, λ _, false.elim⟩) $
λ i s ⟨j, H⟩, let ⟨k, h₁, h₂⟩ := D i j in
⟨k, λ a h, or.cases_on (multiset.mem_cons.1 h)
  (λ h, h.symm ▸ h₁)
  (λ h, trans (H _ h) h₂)⟩

lemma finite.bdd_below_bUnion [semilattice_inf α] [nonempty α] {I : set β} {S : β → set α} (H : finite I) :
  (bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
@finite.bdd_above_bUnion (order_dual α) _ _ _ _ _ H


open filter
variables  {ι' : Type }
lemma unbounded_of_tendsto_at_top' [nonempty α] [semilattice_inf α] [preorder β] [no_top_order β]
  {f : α → β} (h : tendsto f at_bot at_top) :
  ¬ bdd_above (range f) :=
@unbounded_of_tendsto_at_top (order_dual α) _ _ _ _ _ _ h

-- it looks like we only need has_pow here as has_pow is all that appears in the proof
-- however to_monoid and to_inv also appear in the statement, so should not show up
theorem gpow_neg_succ_of_nat' {G : Type } [group G] (a : G) (n : ℕ) : a ^ -[1+n] = (a ^ n.succ)⁻¹ := rfl
-- #printgpow_neg_succ_of_nat

-- #print sum_diff_subset_apply_inr'

-- lemma char_p_iff_char_p' {K L : Type*} [division_ring K] [semiring L] [nontrivial L] (f : K →+* L) (p : ℕ) :
lemma char_p_iff_char_p' {K L : Type*} [field K] [field L] (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
begin
  split;
  { introI _c, constructor, intro n,
    rw [← @char_p.cast_eq_zero_iff _ _ p _c n, ← f.injective.eq_iff, f.map_nat_cast, f.map_zero] }
end
open nat subtype multiset

lemma piecewise_piecewise_of_subset_left' {δ : α → Sort*} (s : finset α) (g f : Π (i : α), δ i) [Π (j : α), decidable (j ∈ s)] {s t : finset α} [Π i, decidable (i ∈ s)]
  [Π i, decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : Π a, δ a) :
  s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
s.piecewise_congr (λ i hi, finset.piecewise_eq_of_mem _ _ _ (h hi)) (λ _ _, rfl)
-- #check       piecewise_piecewise_of_subset_left'

lemma sub_le_of_abs_sub_le_left' {c b a : α} [linear_ordered_ring α] (h : abs (a - b) ≤ c) : b - c ≤ a :=
if hz : 0 ≤ a - b then
  (calc
      a ≥ b     : le_of_sub_nonneg hz
    ... ≥ b - c : sub_le_self _ $ (abs_nonneg _).trans h)
else
  have habs : b - a ≤ c, by rwa [abs_of_neg (lt_of_not_ge hz), neg_sub] at h,
  have habs' : b ≤ c + a, from le_add_of_sub_right_le habs,
  sub_left_le_of_le_add habs'

open_locale big_operators
lemma abs_sum_le_sum_abs [linear_ordered_field α] {f : β → α} {s : finset β} :
  abs (∑ x in s, f x) ≤ ∑ x in s, abs (f x) :=
finset.le_sum_of_subadditive _ abs_zero abs_add s f

end examples

set_option pp.all true
set_option trace.generalising false
-- run_cmd gene
-- #print inv_mul_cancel_left'
-- #print group_with_zero.mul
-- #print mul_action.mem_orbit_self

-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mul_action.mem_orbit_self, aa ← get_instance_chains `mul_action 0 l.value, trace aa --.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mul_action.mem_orbit_self, aa ← is_instance_chain 6 l.value.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body, trace aa--find_gens' cd e l.type l.value 0 ""
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mul_action.mem_orbit_self, trace $ l.value.lambda_body.app_fn.app_fn.app_arg.lambda_body.app_fn.app_arg.app_fn.lambda_body--find_gens' cd e l.type l.value 0 ""
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `char_p_iff_char_p', trace $ find_gens' cd e l.type l.value 0 ""
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `inv_mul_cancel_left', trace $ find_gens' cd e l.type l.value 0 ""
-- run_cmd do e ← get_env, cd ← class_dag e, l← e.get `mul_action.mem_orbit_self, trace $ find_gens' cd e l.type l.value 0 ""


namespace linter
@[linter] meta def generalisation_linter : linter :=
{ test := print_gens_wrap,
  no_errors_found := "no typeclass generalisations found",
  errors_found := "typeclass generalisations may be possible",
  is_fast := ff,
  auto_decls := ff }
end linter
set_option pp.all false
#lint only generalisation_linter
set_option pp.all true
-- meta def aaa :=
-- do l ← find_ancestors `integral_domain (const `int []),
-- generalising_trace l,
-- return ()
-- run_cmd aaa
-- #check and.intro
-- meta def a: tactic unit :=
-- do let e:= (app (const `add_comm_monoid [level.zero]) (const `nat []) : expr),
-- tgt ← return e >>= instantiate_mvars,
--    b   ← is_class tgt,
--    generalising_trace tgt,
--    generalising_trace b,
--    if b then mk_instance tgt >>= generalising_trace
--    else skip,
--    return ()
-- run_cmd a
-- #print reset_instance_cache
/-

Pseudocode:
- For each class C in the type, e.g. [ring H] [topological_ring G] (probably called _inst_1):
  - Find occurences of projections from ring.to_add_comm_group C, ring

-/
-- run_cmd trace (head_eta  $ `(λ (f : ℕ → ℕ), (λ a:ℕ, f a)))--reflect (λ  (f : ℕ → ℕ), (λ a, f + 1)))
-- run_cmd (do e ← get_env,  o← (e.is_projection  `linear_ordered_field.mul_one),
-- trace o.cname,
-- trace o.nparams,
-- trace o.idx,
-- trace o.is_class,
-- return ())
-- #print  int.cast_coe
-- #print  fpow_zero
-- #print  fpow_one
-- #print set.fintype_univ
-- #print set.finite_univ
-- #print finset.disjoint_empty_left
-- -- #print filter.frequently_at_bot'
-- #print quotient_group.coe_mul
-- #print unbounded_of_tendsto_at_top'
-- #print subtype.mk_le_mk
-- #print is_well_order.linear_order
-- #print gpow_of_nat
-- #print gpow_neg_succ_of_nat
-- #print category_theory.category.comp_id
-- #printlist.mem_of_mem_inter_right

-- run_cmd (do
--   e ← get_env,
--   d ← e.get `finset.abs_sum_le_sum_abs,
--   print_gens d,
--   skip)
-- #check linear_ordered_comm_group.to_ordered_add_comm_group
-- #check @linear_ordered_ring.to_linear_order
-- #check @linear_ordered_ring.to_linear_ordered_add_comm_group
-- #check @linear_ordered_ring.to_ordered_ring
-- #check linear_ordered_add_comm_group.to_ordered_add_comm_group
-- run_cmd (do trace $ name.is_internal `set.add_comm_monoid)
-- run_cmd (do curr_env ← get_env,
--   let decls := curr_env.fold [] list.cons,
--   let a:= decls.filter (λ d, declaration.to_name d = `set.add_comm_monoid._proof_3),
--   trace (a.map (λ l, l.to_name.is_internal)))
