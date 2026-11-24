import PEqualNP.Defs

-- Peel the Petersen-minus F8 lower bound (L-meta-1007) from the free-OR elimination bridge.
theorem PEqualNP.Outside.R_meta_2834_2
    (hF8 : ¬ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ)
      (fun (x : Fin (8 : ℕ) → Bool) =>
        x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) ||
        x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) ||
        x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) ||
        x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)) ||
        x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) ||
        x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) ||
        x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
        x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) ||
        x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
        x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))) (12 : ℕ))
    (hBridge :
      ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) →
        x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 →
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        (∀ (x11 : Fin (9 : ℕ) → Bool),
          x3.eval (List.ofFn x11 ++
            [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) =
          (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) ||
           x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) ||
           x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) ||
           x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) ||
           x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) ||
           x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) ||
           x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) ||
           x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) ||
           x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) ||
           x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) ||
           x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) ||
           x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) →
        PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ)
          (fun (x : Fin (8 : ℕ) → Bool) =>
            x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ)) ||
            x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ)) ||
            x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ)) ||
            x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)) ||
            x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ)) ||
            x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) ||
            x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
            x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ)) ||
            x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ)) ||
            x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))) (12 : ℕ)) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) →
      x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 →
      PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
      (∀ (x11 : Fin (9 : ℕ) → Bool),
        x3.eval (List.ofFn x11 ++
          [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) =
        (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) ||
         x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) ||
         x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) ||
         x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) ||
         x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) ||
         x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) ||
         x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) ||
         x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) ||
         x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) ||
         x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) ||
         x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) ||
         x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) → False := by
  intro x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8
  exact hF8 (hBridge x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8)
