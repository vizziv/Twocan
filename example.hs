module Example where

import Coli

exp_F = EFun "x" $ EOp Over (EOp Plus (EVar "x") (EPrim 51)) (EPrim 2)
exp_ApplyTwice = EFun "f" $ EFun "x" $
                 EApp (EVar "f") $ EApp (EVar "f") $ EVar "x"
exp_ApplyTwice_F_17 = EApp (EApp exp_ApplyTwice exp_F) (EPrim 17)

exp_Fact =
    ELet
    "fact"
    (EFun "x" $
     EIfZero
     (EVar "x")
     (EPrim 1)
     (EOp Times (EVar "x")
      (EApp (EVar "fact")
      $ EOp Minus (EVar "x") (EPrim 1))))
    (EVar "fact")
