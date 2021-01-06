import algebra.ring.basic
import generalisation_linter

class foo (X : Type) :=
(f : X → X)
class bar (X : Type) extends foo X :=
(h : f ∘ f = f)

lemma aa (X : Type) [bar X] : (foo.f : X → X) = foo.f := rfl

lemma mn_tors_of_n_tors {X : Type*} [semiring X] (m n : ℕ) (x : X) (h : n •ℕ x = 0) :
  (m * n) •ℕ x = 0 := by rw [mul_nsmul, h, nsmul_zero]
