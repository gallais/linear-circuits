module Circuits.NetList.Interp

import Decidable.Equality

import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers

import Toolkit.Data.Graph.EdgeBounded
import Toolkit.Data.List.DeBruijn
import Toolkit.Data.Whole

import Circuits.NetList.Types
import Circuits.NetList.Terms

%default total

public export
InterpTy : Ty -> Type
InterpTy TyUnit
  = Graph

InterpTy (TyPort x)
  = Pair Vertex Graph

InterpTy (TyChan x)
  = Vertex

InterpTy TyGate
  = Graph

namespace Environments

  public export
  Env : List Ty -> Type
  Env = Env Ty InterpTy

namespace Result

  public export
  data Result : (type : Ty)
                     -> Type
    where
      R : (counter : Nat)
       -> (result  : InterpTy type)
                  -> Result type
  public export
  getResult : Result type -> InterpTy type
  getResult (R _ res) = res

interp : (env     : Env ctxt)
      -> (term    : Term ctxt type)
      -> (counter : Nat)
      -> (graph   : Graph)
                 -> Result type
interp e (Var x) c g
  = R c (read x e)

interp e (Port flow dtype body) c g
  = let c' = S c in
    let s  = size dtype in
    let n = case flow of
              INPUT  => driver  c' s
              OUTPUT => catcher c' s
              INOUT  => gateway c' s
    in
    let e' = extend e (n,g) in
    let g' = insertNode n g
    in  interp e' body c' g'

interp e (Wire dtype body) c g
  = let c' = S c in
    let ch = both c' (size dtype) in
    let e' = extend e ch in
    let g' = insertNode ch g
    in interp e' body c' g'

interp e Stop c g
  = R c g

interp e (Index what idx) c g
  = let R c' (v,g') = interp e what c g in
    let c'' = S c' in
    let i = both c'' 1 in
    let g'' = merge g' g
    in R c'' (i,(insertEdge (ident v, ident i) (insertNode i g'')))

interp e (Mux o s l r) c g
  = let R c'    (o,g1) = interp e o  c    g in
    let R c''   (c,g2) = interp e s  c'   g in
    let R c'''  (a,g3) = interp e l  c''  g in
    let R c'''' (b,g4) = interp e r  c''' g in

    let n = node (S c'''') 3 1 in
    let g = insertNode n (foldr merge g [g1,g2,g3,g4]) in

    let es = [ (ident a, S c''''), (ident b, S c'''')
             , (ident c, S c'''')
             , (S c'''', ident o)
             ]
    in R (S c'''') (foldr (insertEdge) g es)

interp e (GateB k o l r) c g
  = let R c'   (o,g')   = interp e o c   g in
    let R c''  (a,g'')  = interp e l c'  g in
    let R c''' (b,g''') = interp e r c'' g in

    let n = node (S c''') 2 1 in

    let g = insertNode n (foldr merge g [g',g'',g''']) in

    let es = [ (S c''', ident o)
             , (ident a, S c''')
             , (ident b, S c''')
             ]

    in R (S c''') (foldr (insertEdge) g es)

interp e (GateU k o i) c g
  = let R c'  (o,g1)  = interp e o c g in
    let R c'' (i,g2) = interp e i c' g in

    let n  = both (S c'') 1    in
    let g3 = insertNode n (foldr merge g [g1,g2]) in

    let es = [(S c'', ident o), (ident i, S c'')]

    in R (S c'') (foldr insertEdge (merge g3 g) es)

interp e (GateDecl x body) c g
  = let R c' g' = interp e x c g
    in interp (extend e g') body c' g'

interp e (Project how chan) c g
  = let c' = S c in
    let epoint = both c' 1 in

    let R c'' chan' = interp e chan c' g in
    let ed = case how of
               WRITE => (c',     ident chan')
               READ  => (ident chan', c')
    in
    let g' = insertEdge ed (insertNode epoint g)
    in R c'' (epoint,g')

interp e (Cast how what) c g
  = let c' = S c in
    let ca = both c' 1 in
    let R c'' (w',g') = interp e what c' g in
    let ed = case how of
               BO => (c'      , ident w')
               BI => (ident w', c')
    in
    let g'' = insertEdge ed (insertNode ca g)
    in R c'' (ca, merge g'' g')


public export
data Valid : (type : Ty) -> InterpTy type -> Type where
  P : Valid (TyPort x) v
  G : (g : Graph) -> ValidGraph g -> Valid TyGate g
  D : (g : Graph) -> ValidGraph g -> Valid TyUnit g
  C : Valid (TyChan x) v

isValid : {type : Ty}
       -> (g    : InterpTy type)
               -> Dec (Valid type g)

isValid {type = TyUnit} g with (validGraph g)
  isValid {type = TyUnit} g | (Yes prf)
    = Yes (D g prf)
  isValid {type = TyUnit} g | (No contra)
    = No (\(D g prf) => contra prf)

isValid {type = (TyPort x)} g
  = Yes P

isValid {type = (TyChan x)} g
  = Yes C

isValid {type = TyGate} g with (validGraph g)
  isValid {type = TyGate} g | (Yes prf)
    = Yes (G g prf)
  isValid {type = TyGate} g | (No contra)
    = No (\(G g prf) => contra prf)

export
run : (term : Term Nil TyUnit)
           -> Dec (Valid TyUnit (getResult (interp Nil term Z (MkGraph Nil Nil))))
run term with (interp Nil term Z (MkGraph Nil Nil))
  run term | R cout gout with (validGraph gout)
    run term | R cout gout | (Yes prf)
      = Yes (D gout prf)
    run term | R cout gout | (No contra)
      = No (\(D g prf) => contra prf)

export
runIO : (term : Term Nil TyUnit)
             -> IO (Maybe (g ** Valid TyUnit g))
runIO term with (interp Nil term Z (MkGraph Nil Nil))
  runIO term | (R counter result) with (validGraph result)
    runIO term | (R counter (MkGraph vs es)) | (Yes (IsValid x))
      = pure (Just ((MkGraph vs es) ** D (MkGraph vs es) (IsValid x)))
    runIO term | (R counter result) | (No contra)
      = pure Nothing

-- [ EOF ]
