module Circuits.Idealised.Denotation

import Circuits.Idealised.Types
import Circuits.Idealised.Terms
import Circuits.Split

import Data.List.Elem
import Data.List.Quantifiers

import Data.Nat
import Data.Fin
import Data.Linear
import Data.Linear.List.LQuantifiers
import Data.Linear.LVect
import Data.Linear.Bifunctor
import Data.Linear.Copies
import Toolkit.Data.Whole

%default total

dType : DType -> Type
dType LOGIC = Bool
dType (BVECT (W n prf) a) = LVect n (dType a)

Eq Direction where
  INPUT == INPUT = True
  OUTPUT == OUTPUT = True
  _ == _ = False

Inverse : Type -> Type
Inverse a = a -@ ()

Resource : Ty -> Usage -> Type
Resource _ USED = ()
Resource (TyPort (dir, ty)) FREE = ifThenElse (dir == INPUT) id Inverse (dType ty)
Resource _ _ = ()

Resources : List (Ty, Usage) -> Type
Resources = LAll (uncurry Resource)

denoteVar : {0 prf : Elem (ty, FREE) ins} ->
            Resources ins -@
            Use ins prf ous -@
            LPair (Resource ty FREE) (Resources ous)
denoteVar (v :: vs) H = v # (() :: vs)
denoteVar (v :: vs) (T x) =
  let (w # ws) = denoteVar vs x in
  (w # v :: ws)

denoteUsed : All Used ins -> Resources ins -@ ()
denoteUsed [] [] = ()
denoteUsed (IsUsed :: prf) (v :: vs) = v `seq` denoteUsed prf vs

DUP : (d : DType) -> Duplicable (dType d)
DUP LOGIC = %search
DUP (BVECT (W n prf) d) = aux (DUP d) where
  aux : Duplicable a -> Duplicable (LVect n a)
  aux = %search

CON : (d : DType) -> Consumable (dType d)
CON LOGIC = %search
CON (BVECT (W n prf) d) = aux (CON d) where
  aux : Consumable a -> Consumable (LVect n a)
  aux = %search

copy : (d : DType) -> dType d -@ LPair (dType d) (dType d)
copy d v = pair (duplicate @{DUP d} v) where

ifThenElse : Consumable a => Bool -@ a -@ a -@ a
ifThenElse True  t f = f `seq` t
ifThenElse False t f = t `seq` f

not : Bool -@ Bool
not b = ifThenElse b False True

(&&) : Bool -@ Bool -@ Bool
iA && iB = ifThenElse iA iB False

(||) : Bool -@ Bool -@ Bool
iA || iB = ifThenElse iA True iB

xor : Bool -@ Bool -@ Bool
True  `xor` iB = not iB
False `xor` iB = iB

denoteGate : GateKind -@ Bool -@ Bool -@ Bool
denoteGate AND  iA iB = iA && iB
denoteGate IOR  iA iB = iA || iB
denoteGate XOR  iA iB = iA `xor` iB
denoteGate ANDN iA iB = not (iA && iB)
denoteGate IORN iA iB = not (iA || iB)
denoteGate XORN iA iB = not (iA `xor` iB)
denoteGate JOIN iA iB = ?gate -- TODO: what is this?

denoteIndex : {sn : Whole} ->
              Index sn pivot n -@ dType (BVECT sn a) -@ LPair (dType a) (dType (BVECT n a))
denoteIndex First = lookup FZ
denoteIndex Last  = lookup last

denote : Resources ins -@
         Term ins ty ous -@
         LPair (Resource ty FREE) (Resources ous)
denote vs (Var prf x) = denoteVar vs x
denote vs (NewSignal flow datatype body) = ?a_1
denote vs (Wire datatype body) = denote (?out :: ?inp :: vs) body
denote vs (Mux {datatype} output control inputA inputB) =
  let (k  # vs) = denote vs output in
  let (c  # vs) = denote vs control in
  let (iA # vs) = denote vs inputA in
  let (iB # vs) = denote vs inputB in
  let 1 res = ifThenElse @{CON datatype} c iA iB in
  k res `seq` (() # vs)
denote vs (Dup {datatype} outA outB input) =
  let (k1 # vs) = denote vs outA in
  let (k2 # vs) = denote vs outB in
  let (v  # vs) = denote vs input in
  let (v1 # v2) = copy datatype v in
  k1 v1 `seq` k2 v2 `seq` (() # vs)
denote vs (Seq x y) =
  let (v # vs) = denote vs x in
  v `seq` denote vs y
denote vs (Not output input) =
  let (k # vs) = denote vs output in
  let (b # vs) = denote vs input in
  k b `seq` (() # vs)
denote vs (Gate kind output inputA inputB) =
  let (k  # vs) = denote vs output in
  let (iA # vs) = denote vs inputA in
  let (iB # vs) = denote vs inputB in
  let res = denoteGate kind iA iB in
  k res `seq` (() # vs)
denote vs (IndexSingleton output input) =
  let (k # vs) = denote vs output in
  let ([v] # vs) = denote vs input in
  k v `seq` (() # vs)
denote vs (IndexEdge pivot idx outu outf input) =
  let (ku # vs) = denote vs outu in
  let (kf # vs) = denote vs outf in
  let (bs # vs) = denote vs input in
  let (b  # bs) = denoteIndex idx bs in
  ku b `seq` kf bs `seq` (() # vs)
denote vs (IndexSplit pivot idx usedA freeA freeB input) =
  let (ku  # vs) = denote vs usedA in
  let (kfA # vs) = denote vs freeA in
  let (kfB # vs) = denote vs freeB in
  let (i   # vs) = denote vs input in
  (?a_11 # vs)
denote vs (Merge2L2V output inputA inputB) =
  let (k  # vs) = denote vs output in
  let (iA # vs) = denote vs inputA in
  let (iB # vs) = denote vs inputB in
  k [iA,iB] `seq` (() # vs)
denote vs (Merge2V2V prf output inputA inputB) =
  let (k  # vs) = denote vs output in
  let (iA # vs) = denote vs inputA in
  let (iB # vs) = denote vs inputB in
  (?oj # vs)
denote vs (MergeSingleton output input) =
  let (k # vs) = denote vs output in
  let (i # vs) = denote vs input in
  k [i] `seq` (() # vs)
denote vs (Stop prf) = (denoteUsed prf vs # [])
