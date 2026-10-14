import Matmul.IntegralConvolutionReduction
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.AdjoinRoot

/-!
# Concrete finite free integer models of finite-field extensions

A primitive power basis over `ZMod p` has a monic minimal polynomial.
Lift that polynomial to the integers, retaining its degree and monicity.
The resulting `AdjoinRoot` is free over the integers and maps to the given
field with compatible power bases.
-/

namespace Matmul.IntegralConvolution

set_option backward.isDefEq.respectTransparency false

open Module Polynomial
open scoped BigOperators

theorem exists_integer_model_of_powerBasis {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [Algebra (ZMod p) F]
    (pb : PowerBasis (ZMod p) F) :
    ∃ g : ℤ[X], ∃ hg : g.Monic, ∃ φ : AdjoinRoot g →+* F,
      ∃ bK : Basis (Fin g.natDegree) (ZMod p) F,
        0 < g.natDegree ∧
        (∀ i, φ ((AdjoinRoot.powerBasis' hg).basis i) = bK i) ∧
        φ (AdjoinRoot.root g) = pb.gen := by
  classical
  let f := minpoly (ZMod p) pb.gen
  have hf : f.Monic := minpoly.monic pb.isIntegral_gen
  have hlift : f ∈ Polynomial.lifts (Int.castRingHom (ZMod p)) :=
    Polynomial.mem_lifts_of_surjective ZMod.intCast_surjective f
  obtain ⟨g, hgmap, hgdegree, hg⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift hf
  have hd : g.natDegree = pb.dim := hgdegree.trans pb.natDegree_minpoly
  have hcomp : (algebraMap (ZMod p) F).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom F := by ext n; simp
  have heval : g.eval₂ (Int.castRingHom F) pb.gen = 0 := by
    rw [← hcomp, ← Polynomial.eval₂_map, hgmap]
    exact minpoly.aeval (ZMod p) pb.gen
  let φ := AdjoinRoot.lift (Int.castRingHom F) pb.gen heval
  have hroot : φ (AdjoinRoot.root g) = pb.gen := AdjoinRoot.lift_root heval
  let bK := pb.basis.reindex (finCongr hd.symm)
  refine ⟨g, hg, φ, bK, by rw [hd]; exact pb.dim_pos, ?_, hroot⟩
  change ∀ i : Fin g.natDegree, φ ((AdjoinRoot.powerBasis' hg).basis i) = bK i
  intro i
  rw [(AdjoinRoot.powerBasis' hg).basis_eq_pow, map_pow]
  change φ (AdjoinRoot.root g) ^ i.val = bK i
  rw [hroot]
  change pb.gen ^ i.val = (pb.basis.reindex (finCongr hd.symm)) i
  rw [Basis.reindex_apply, pb.basis_eq_pow]
  rfl

#print axioms exists_integer_model_of_powerBasis

/-- For any prescribed prime and any finite number of interpolation nodes,
there is a concrete monic integer quotient algebra whose Vandermonde norm
avoids that prime. The quotient is finite free over the integers. -/
theorem exists_prime_avoiding_nodes (p N : ℕ) (hp : p.Prime) :
    ∃ g : ℤ[X], ∃ hg : g.Monic, 0 < g.natDegree ∧
      ∃ nodes : Fin N → AdjoinRoot g,
        ¬ (p : ℤ) ∣ Algebra.norm ℤ (Matrix.vandermonde nodes).det := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p (N + 1)
  letI : Fintype F := Fintype.ofFinite F
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) F
  obtain ⟨g, hg, φ, bK, hd, hb, hroot⟩ := exists_integer_model_of_powerBasis pb
  let bZ := (AdjoinRoot.powerBasis' hg).basis
  have hsurj : Function.Surjective φ :=
    surjective_of_compatible_zmod_basis bZ bK φ hb
  have hpow : N ≤ p ^ (N + 1) := by
    have htwo := (N + 1).lt_two_pow_self
    have hmono := Nat.pow_le_pow_left hp.two_le (N + 1)
    omega
  have hcard : Fintype.card (Fin N) ≤ Fintype.card F := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact (GaloisField.card p (N + 1) (by omega)).symm ▸ hpow
  obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le hcard
  choose nodes hnodes using fun i : Fin N => hsurj (a i)
  have hdet : φ (Matrix.vandermonde nodes).det = (Matrix.vandermonde a).det := by
    rw [φ.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.vandermonde_apply, map_pow, hnodes]
  have hnorm : (Algebra.norm ℤ (Matrix.vandermonde nodes).det : ZMod p) ≠ 0 := by
    rw [norm_map_of_compatible_basis bZ bK φ hb]
    letI : Module.Free (ZMod p) F := Module.Free.of_basis bK
    letI : Module.Finite (ZMod p) F := Module.Finite.of_basis bK
    apply Algebra.norm_ne_zero_iff.mpr
    rw [hdet]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr a.injective
  refine ⟨g, hg, hd, nodes, ?_⟩
  exact fun hdiv => hnorm ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv)

#print axioms exists_prime_avoiding_nodes

end Matmul.IntegralConvolution
