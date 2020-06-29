import ring_theory.ideals

import ring_theory.principal_ideal_domain

universe u

class discrete_valuation_ring (R : Type u) extends principal_ideal_domain R :=

(prime_ideal' : ideal R)

(primality : prime_ideal'.is_prime)

(is_nonzero : prime_ideal' ≠ ⊥)

(unique_nonzero_prime_ideal : ∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = prime_ideal')

namespace discrete_valuation_ring

def prime_ideal (R : Type u) [discrete_valuation_ring R] : ideal R :=
discrete_valuation_ring.prime_ideal'

instance is_prime (R : Type*) [discrete_valuation_ring R] : (prime_ideal R).is_prime :=
primality

variables {R : Type u} [discrete_valuation_ring R]
open principal_ideal_domain
open discrete_valuation_ring

lemma prime_ideal_is_maximal : (prime_ideal R).is_maximal :=
begin
  have f : prime_ideal R ≠ ⊥,
  { apply discrete_valuation_ring.is_nonzero },
  apply is_prime.to_maximal_ideal,
    exact f,
end

lemma unique_max_ideal : ∃! I : ideal R, I.is_maximal :=

begin

  use prime_ideal R,

  split,

  { exact prime_ideal_is_maximal },

  { intros y a,

    cases discrete_valuation_ring.unique_nonzero_prime_ideal y a.is_prime,

    { exfalso,

      rw h at a,

      apply discrete_valuation_ring.primality.left,

      exact a.right (prime_ideal R) (bot_lt_iff_ne_bot.2 discrete_valuation_ring.is_nonzero) },

    { assumption } }

end

instance is_local_ring : local_ring R := local_of_unique_max_ideal unique_max_ideal

open principal_ideal_domain
open local_ring

lemma local_pid_dvr {S : Type u} (is_local : local_ring S) (pid: principal_ideal_domain S) (non_field : local_ring.nonunits_ideal S ≠ ⊥ ) : discrete_valuation_ring S :=
begin
use local_ring.nonunits_ideal S,
rw zero_mem_nonunits,
sorry,
end

end discrete_valuation_ring

