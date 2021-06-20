import data.real.basic

-- https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/lemma.20distribution/near/212269963
-- see also https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/lemma.20distribution/near/212255452


meta def expr.get_constants (e : expr) : name_set :=
e.fold mk_name_set $ λ e' _ s, match e' with
| expr.const nm _ := s.insert nm
| _ := s
end

meta def declaration.get_constants : declaration → name_set
| (declaration.ax nm _ tp) := tp.get_constants
| (declaration.cnst nm _ tp is_meta) := tp.get_constants
| (declaration.thm nm _ tp bd) := tp.get_constants.union bd.get.get_constants
| (declaration.defn nm _ tp bd _ is_meta) := tp.get_constants.union bd.get_constants

namespace tactic

meta def module_info_of_decl (n : name) : tactic module_info :=
do e ← get_env,
match e.decl_olean n with
| some s := return $ module_info.of_module_id s
| none := failed
end

meta def get_env_of (n : name) : tactic environment :=
do e ← get_env,
match e.decl_olean n with
| some s := return $ environment.for_decl_of_imported_module s n
| none := fail!"couldn't find {n}"
end

meta def test_names_at (ns : name_set) (tgt : name) : tactic bool :=
do e ← get_env_of tgt,
   return $ ns.fold tt $ λ nm b, b && e.contains nm

meta def find_highest (tgt : name) : tactic name :=
do d ← get_decl tgt,
let cnsts := d.get_constants,
cnsts.to_list.mfirst (λ nm,
  test_names_at (cnsts.erase nm) nm >>= guardb >> return nm) <|>
fail "didn't find any highest decl"

meta def locate_decl (tgt : name) : tactic unit :=
do highest ← find_highest tgt,
   e ← get_env,
   let file := match e.decl_olean highest with
   | none := "the current file"
   | some s := (module_info.of_module_id s).id
   end,
   trace!"{tgt} belongs in {file} after {highest}"

end tactic

lemma real_big : (3000 : ℝ) + 2 > 50 := by norm_num

def recfn : ℕ → ℕ
| 0 := 0
| (n+1) := n

run_cmd tactic.locate_decl ``real_big
-- real_big belongs in /Storage/lean/mathlib/src/data/real/basic.lean after real.has_add

#print recfn
run_cmd tactic.locate_decl ``recfn
