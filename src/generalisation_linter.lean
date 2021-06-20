import dag
import utils
import tactic

/-! # Generalisation linter

This file defines a linter to find generalisations.
-/

open native

declare_trace generalising
set_option trace.generalising false

/-- A shorthand for tracing when the `trace.generalising` option is set to true. -/
meta def generalising_trace {α} [has_to_tactic_format α] (s : α) : tactic unit :=
tactic.when_tracing `generalising (tactic.trace s)

-- TODO check
-- +++ b/src/topology/algebra/ordered.lean
-- @@ -1630,8 +1630,8 @@ funext $ assume f, map_eq_comap_of_inverse (funext neg_neg) (funext neg_neg)

--  section topological_add_group

-- -variables [topological_space α] [ordered_add_comm_group α] [topological_add_group α]
-- -
-- +variables [topological_space α] [add_group α] [topological_add_group α]
-- +#check order_closed_topology
-- TODO use expr.occurs
-- TODO bad7pibinder
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
open tactic declaration environment
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

open expr
/-- A bound class is what we will search through, most commonly this is just a name of a class
    e.g. `ring` but sometimes we wish to distinguish bound arguments, e.g. `has_pow α ℕ` should
    be distinct from `has_pow α ℤ`.
-/
@[derive decidable_eq]
meta structure bound_class :=
(name : name)
(bindings : list expr)
-- TODO instance arguments should also be replaced here?
-- currently t2_space #0 topology_from_metric ≠ t2_space #0 topology_from_some_other_method
meta def expr.to_bound_class (e : expr) : bound_class :=
⟨e.get_app_fn.const_name, e.get_app_args.map
  (λ e, (e.replace (λ e n, match e with
    | var n := some (var 0)
    | e := none
    end)))⟩
meta def declaration.to_bound_class (d : declaration) : bound_class :=
  d.type.erase_annotations.pi_binders.snd.to_bound_class

meta def name.to_bound_class (n : name) : tactic bound_class := declaration.to_bound_class <$> get_decl n
namespace bound_class
-- it is important that this lt is total otherwise it seems rb_map misbehaves
meta instance : has_lt bound_class := ⟨λ b₁ b₂, b₁.name < b₂.name ∨ (b₁.name = b₂.name ∧ (list.lex (λ e e', e < e') b₁.bindings b₂.bindings))⟩
meta instance : decidable_rel ((<) : bound_class → bound_class → Prop) := by apply_instance
meta instance : has_to_format bound_class := ⟨λ bi, bi.name.to_string ++ " "
  ++ " ".intercalate (bi.bindings.map (has_to_string.to_string)) ⟩
meta instance : has_to_string bound_class := ⟨λ bi, bi.name.to_string
-- ++ " " ++ " ".intercalate (bi.bindings.map (expr.to_string)) -- TMI most of the time
⟩

meta instance : inhabited bound_class := { default := { name := `no_meet_fake_name,
  bindings := [] } }

end bound_class

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
meta def class_dag (env : environment) : tactic (dag bound_class) :=
do t ← env.mfold (dag.mk bound_class)
  (λ decl a, let name := decl.to_name in do
    tactic.has_attribute `instance name >> (do
      (l, tgt) ← return decl.type.pi_binders,
      -- guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
      guard (l.tail.all $ λ b, (b.info = binder_info.inst_implicit) || (b.info = binder_info.implicit)),
      guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var), -- TODO check these conditions
      guard l.head.type.is_sort,
      generalising_trace name,
      -- generalising_trace l,
      -- generalising_trace tgt,
      -- generalising_trace decl.to_bound_class,
      let src := l.ilast.type.to_bound_class,
      let tgt := decl.to_bound_class,
      guard (src ≠ tgt),
      generalising_trace $ has_to_format.to_format src ++ " → " ++ has_to_format.to_format tgt,
      return (a.insert_edge src tgt)) <|>
      return a),
  trace "dag gend",
  return t
  -- set_option trace.generalising true
  -- run_cmd (get_env >>= class_dag)
  -- run_cmd (get_env >>= class_dag >>= trace)

-- set_option pp.all true
-- TODO
    -- #check mul_action.to_has_scalar -- want this
    -- #check ring_hom.has_coe_to_fun -- not this
  -- run_cmd do decl ← get_decl `mul_action.to_has_scalar,
  -- #print nat.cast_coe
  -- run_cmd do decl ← get_decl `nat.cast_coe,
  --   let name := decl.to_name in do
  --   tactic.has_attribute `instance name >> (do
  --     (l, tgt) ← return decl.type.pi_binders,
  --     generalising_trace l,
  --     generalising_trace tgt,
  --     guard (l.tail.all $ λ b, (b.info = binder_info.inst_implicit) || (b.info = binder_info.implicit)),
  --     generalising_trace l.tail,
  --     generalising_trace tgt.get_app_args,
  --     guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
  --     generalising_trace l.head,
  --     guard l.head.type.is_sort,
  --     generalising_trace name,
  --     generalising_trace l,
  --     generalising_trace tgt,
  --     let src := l.ilast.type.erase_annotations.get_app_fn.const_name,
  --     let tgt := tgt.erase_annotations.get_app_fn.const_name,
  --     guard (src ≠ tgt),
  --     trace ((dag.mk _root_.name).insert_edge src tgt)) <|>
  --     trace (dag.mk _root_.name)

meta def print_dag : tactic unit := do c ← get_env, class_dag c >>= trace
-- run_cmd print_dag
meta def print_div (l : list bound_class) : tactic unit :=
do c ← get_env,
  class_dag c >>= (λ d, trace $ d.minimal_vertices (native.rb_set.of_list l))
meta def print_div' (l : list bound_class) : tactic unit :=
do c ← get_env,
  class_dag c >>= (λ d, trace $ d.meets_of_components (native.rb_set.of_list l))
-- run_cmd print_div' [ ⟨`linear_order,[var 0]⟩, ⟨`linear_ordered_add_comm_group,[var 0]⟩,
  -- ⟨`ordered_ring ,[var 0]⟩ ]

-- run_cmd print_div' [ ⟨`group,[var 0]⟩ ]
-- #print noetherian_ring
-- run_cmd print_div' [ ⟨`comm_semiring,[var 0]⟩,⟨`ring,[var 0]⟩,⟨`noetherian_ring,[var 0]⟩ ]
-- run_cmd print_div [ ⟨`has_add,[var 0]⟩, ⟨ `has_zero,[var 0]⟩, ⟨ `add_monoid,[var 0]⟩,
--   ⟨ `has_zero,[var 0]⟩, ⟨ `has_add,[var 0]⟩, ⟨`add_monoid ,[var 0]⟩]
-- run_cmd print_div [ ⟨`has_pow,[var 0, `(int)]⟩,
-- ⟨`has_pow,[var 0, `(nat)]⟩,
-- ⟨`monoid,[var 0]⟩]
-- #eval to_bool $ (⟨`has_pow,[var 0, `(int)]⟩ :bound_class) < ⟨`has_pow,[var 0, `(nat)]⟩

open dag

meta def print_reachable (n : bound_class) : tactic unit :=
do
  c ← get_env,
  -- d ← get_decl a,
  t ← class_dag c,
  trace (reachable t n),
  return ()
meta def print_tos_reachable (n : bound_class) : tactic unit :=
do
  c ← get_env,
  -- d ← get_decl a,
  t ← class_dag c,
  trace $ topological_sort (reachable t n),
  return ()
-- run_cmd print_reachable ⟨`linear_ordered_ring, [var 0]⟩
-- run_cmd print_tos_reachable ⟨`linear_ordered_ring, [var 0]⟩
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
  generalising_trace pots,
  return names

/- These types aliases are banned as they look like they could be generalisations, i.e. why
   assume `has_add α` when all you need is `has_add (order_dual α)`, but in these cases
   the classes are equivalent, likewise with prod we have addition on the prod iff addition
   on each component so most often we do not gain anything by removing these.
-/
def banned_aliases : list name := [`order_dual, `multiplicative, `additive, `prod]

set_option pp.all true
meta def is_instance_chain : ℕ → expr → tactic bool := λ n e, do
  (do
    guardb e.is_app,
    tactic.has_attribute `instance e.get_app_fn.const_name,
    l ← e.get_app_args.mfoldl (λ ol arg, (&& ol) <$> (tactic.head_eta arg >>= is_instance_chain n)) tt,
    d ← get_decl e.get_app_fn.const_name,
    guard d.type.pi_binders.2.get_app_args.head.is_var,-- && l.ilast.type.get_app_args.head.is_var),
    return l)
  <|> (do
    m ← e.match_var,
    --guardb (n ≤ m), -- TODO this might be excessive if later tcs also used
    return tt) <|> (do
  return ff)
  set_option trace.generalising false

-- set_option profiler true
meta def target (cla : bound_class) (t : expr) (n : ℕ) : tactic bound_class :=
do e ← get_env,
  generalising_trace "tgt",
  generalising_trace t,
  (do m ← t.match_var, -- if this is just a variable (i.e. chain of length 0 return)
    guardb (n = m),
    return cla) <|> (do
  t ← e.get t.get_app_fn.const_name,
  return t.to_bound_class
  -- (l, tgt) ← return t.type.pi_binders,
  -- generalising_trace l,
  -- generalising_trace tgt,
  -- guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
  -- guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
  -- let src := l.ilast.type.erase_annotations.get_app_fn.const_name,
  -- let tgt := tgt.erase_annotations.get_app_fn.const_name,
  -- generalising_trace tgt,
  -- return tgt
  )

open native.rb_set
-- meta def trace_and_return (ss:string){X : Type*} [has_to_format X] (x : tactic X): tactic X := do l ←  x, trace ("out"++ss), trace l, return l
/-- Gets chains of instances containing variable n in the expr, varible should have type cla : name when instantiated.
  TODO example
  -/
meta def get_instance_chains (cla : bound_class) : ℕ → expr → tactic (native.rb_set bound_class) := λ n e, do
  -- generalising_trace $ "considering " ++ to_string e ++ " " ++ to_string n,
  boo ← is_instance_chain n e,
  if boo then
    (do
      generalising_trace $ "inst chain",
      generalising_trace $ e.get_app_fn,
      guardb $ e.has_var_idx n, -- does the chain contain the instance we are generalising?
      if e.get_app_fn.const_name.get_prefix ∉ banned_aliases -- does the instance chain end in a banned type alias?
      then
      do
        generalising_trace $ "contains " ++ to_string n,
        tar ← target cla e n,
        return $ mk_rb_set.insert tar
      else
        return $ mk_rb_set.insert cla
      ) <|> return mk_rb_set
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
--   run_cmd print_div [`has_scalar,`mul_action]
--   run_cmd print_reachable `has_scalar
--   run_cmd print_reachable `mul_action
--   run_cmd print_dag

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
-- #print char_p.cast_card_eq_zero
-- find the typeclass generalisations possible in a given decl
-- input should be the type and then the body
-- TODO env not needed?
meta def find_gens' (de : declaration) (cd : dag bound_class) (env : environment) : expr → expr → ℕ → string → tactic (option string)
-- we match the binders on the type and body simultaneously
| (pi tna binder_info.inst_implicit tty tbody) (lam na binder_info.inst_implicit ty body) n s := do
  -- We are now trying to generalise `tna` which is of type `tty`
  generalising_trace $ "type-type " ++ to_string tty,
  generalising_trace $ "type " ++ to_string ty,
  if tty ≠ ty then trace "WARNING types not equal" >> trace de else skip,
  (do guard tty.get_app_fn.is_constant, -- for now we ignore things like [∀ i, decidable_eq $ f i]
    -- generalising_trace $ "body " ++ to_string body,
    -- generalising_trace "n ",
    -- generalising_trace n,
    ou  ← get_instance_chains tty.to_bound_class 0 body,
    tou ← get_instance_chains tty.to_bound_class 0 tbody,
    generalising_trace ou,
    generalising_trace tou,
    let ans := (λ u, (cd.meets_of_components u).union $ u.filter (λ v, ¬ cd.contains v)) (ou.union tou),
    generalising_trace ans,
    -- do unused separety
    --  guard ((ans.size = 0) && (¬us')) >>
    --    (find_gens' tbody body (n + 1) (s ++ "unused_arg ? " ++ "\n" ++ ty.to_string ++ "\n" ++ ts'.to_string ++ "\n" ++ na.to_string)) <|>
    -- guard ((ts'.length = 0) && (¬us')) >>
    --   (find_gens' tbody body (n + 1) (s ++ "unused_arg ? " ++ "\n" ++ ty.to_string ++ "\n" ++ ts'.to_string ++ "\n" ++ na.to_string)) <|>
    guard (¬ ans.contains tty.to_bound_class), -- this probably shouldn't happen?
    --  && (¬us')
    generalising_trace ans,
    guard (tty.get_app_fn.const_name.get_prefix ∉ banned_aliases), -- TODO check if this actually does anything
    generalising_trace ans,
    --  has_attribute `instance ts'.head.const_name >>
    find_gens' tbody body (n + 1) (s ++ na.to_string ++ ": " ++
      ty.get_app_fn.const_name.to_string ++ " ↝" ++
      ((ans.to_list.map (to_string)).qsort (λ a b, a < b)).foldl (λ ol n, ol ++ " " ++ n) "" ++ -- sort the output
      "\n")) <|>
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
meta def print_gens (cd : dag bound_class) (decl : declaration) : tactic (option string) :=
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
  find_gens' decl cd env decl.type decl.value 0 ""
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
meta def dag_attr : user_attribute (dag bound_class) unit := {
  name := "_dag",
  descr := "(internal) attribute just to store the class dag",
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
-- set_option pp.all false
-- #lint only generalisation_linter
-- set_option pp.all true
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
