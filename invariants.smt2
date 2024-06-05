; synthèse d'invariant de programme
; on déclare le symbole non interprété de relation Invar
(declare-fun Invar (Int Int) Bool)
; la relation Invar est un invariant de boucle
(assert (forall (( i Int ) ( v Int ))
(=> (and (Invar i v) (< 0 i)) (Invar (- i 1) (+ v i)))))
; la relation Invar est vraie initialement
(assert (Invar 4 0))
; l'assertion finale est vérifiée
(assert (forall (( i Int ) ( v Int ))
(=> (and (Invar i v) (<= i 0)) (= v 10))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)
(exit)