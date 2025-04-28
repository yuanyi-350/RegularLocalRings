import Mathlib

lemma Ideal.height_le_spanRank_toENat_of_mem_minimal_primes {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ I.spanRank.toENat := sorry

lemma Ideal.height_le_spanRank_toENat {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ I.spanRank.toENat := sorry

lemma Ideal.height_le_spanFinrank {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    I.height ≤ I.spanFinrank := sorry
