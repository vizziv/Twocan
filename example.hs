module Example where

import Twocan
import qualified Data.Map as M

exp_F = EFun "x" $ EOp Over (EOp Plus (EVar "x") (EPrim 51)) (EPrim 2)
exp_ApplyTwice = EFun "f" $ EFun "x" $
                 EApp (EVar "f") $ EApp (EVar "f") $ EVar "x"
exp_ApplyTwice_F_17 = EApp (EApp exp_ApplyTwice exp_F) (EPrim 17)

-- A parser is getting more and more desirable....

exp_Unit = EProd M.empty

exp_Le = EFun "x" $ EFun "y" $
         EBranch (EOp Minus (EVar "x") (EVar "y"))
         (ESum "True" exp_Unit)
         (ESum "False" exp_Unit)

exp_Fact =
    ELet "fact"
    (EFun "x"
     (EBranch (EVar "x")
      (EPrim 1)
      (EOp Times (EVar "x")
       (EApp
        (EVar "fact")
        (EOp Minus (EVar "x") (EPrim 1))))))
    (EVar "fact")

exp_Fib =
    ELet "fib"
    (EFun "x"
     (ELet "n" (EProj "N" (EVar "x"))
      (EBranch (EOp Minus (EVar "n") (EPrim 0))
       (EProj "F0" (EVar "x"))
       (EApp (EVar "fib")
        (EProd $ M.fromList
         [("N", EOp Minus (EVar "n") (EPrim 1)),
          ("F0", (EProj "F1" (EVar "x"))),
          ("F1", EOp Plus
           (EProj "F0" (EVar "x"))
           (EProj "F1" (EVar "x")))])))))
    (EFun "n"
     (EApp (EVar "fib")
      (EProd $ M.fromList
       [("N", EVar "n"),
        ("F0", EPrim 0),
        ("F1", EPrim 1)])))

exp_FibWithCase =
    ELet "fib"
    (EFun "x"
     (ELet "n" (EProj "N" (EVar "x"))
      (ECase (EApp (EApp exp_Le (EVar "n")) (EPrim 0)) $ M.fromList
       [("True", EFun "_" (EProj "F0" (EVar "x"))),
        ("False",
         EFun "_"
         (EApp (EVar "fib")
          (EProd $ M.fromList
           [("N", EOp Minus (EVar "n") (EPrim 1)),
            ("F0", (EProj "F1" (EVar "x"))),
            ("F1", EOp Plus
             (EProj "F0" (EVar "x"))
             (EProj "F1" (EVar "x")))])))])))
    (EFun "n"
     (EApp (EVar "fib")
      (EProd $ M.fromList
       [("N", EVar "n"),
        ("F0", EPrim 0),
        ("F1", EPrim 1)])))

exp_Map = EFun "f"
          (ELet "map"
           (EFun "xs"
            (ECase (EVar "xs") $ M.fromList
             [("Nil", EFun "_" (EVar "xs")),
              ("Cons",
               EFun "cons"
               (EProd $ M.fromList
                [("Head", EApp (EVar "f") (EProj "Head" (EVar "cons"))),
                 ("Tail", EApp (EVar "map") (EProj "Tail" (EVar "cons")))]))]))
           (EVar "map"))

mkList = foldr (\ x xs -> ESum "Cons" . EProd $ M.fromList
                [("Head", x), ("Tail", xs)])
               (ESum "Nil" exp_Unit)

exp_Map_Fact_125 = EApp (EApp exp_Map exp_Fact) $ mkList $ map EPrim [1,2,5]
