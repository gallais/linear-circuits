module Circuits.Idealised.Parser

import Data.Nat
import Data.List1

import Text.Lexer
import Text.Parser

import Toolkit.Data.Whole
import Toolkit.Data.Location
import Toolkit.Text.Lexer.Run
import Toolkit.Text.Parser.Support
import Toolkit.Text.Parser.Location
import Toolkit.Text.Parser.Run

import Ref

import Circuits.Idealised.Types
import Circuits.Idealised.AST
import Circuits.Idealised.Lexer

%default total

namespace Idealised
  public export
  Rule : Type -> Type
  Rule = Rule Unit Token

  public export
  RuleEmpty : Type -> Type
  RuleEmpty = RuleEmpty Unit Token

  export
  eoi : RuleEmpty Unit
  eoi = eoi isEOI
    where
      isEOI : Token -> Bool
      isEOI EndInput = True
      isEOI _ = False

namespace API
  export
  symbol : String -> Rule Unit
  symbol str
    = terminal ("Expected Symbol '" ++ str ++ "'")
               (\x => case x of
                             Symbol s => if s == str then Just MkUnit
                                                     else Nothing
                             _ => Nothing)

  export
  nat : Rule Nat
  nat = terminal "Expected nat literal"
               (\x => case x of
                           LitNat i => Just i
                           _ => Nothing)

  export
  keyword : String -> Rule Builtin.Unit
  keyword str
    = terminal ("Expected Keyword '" ++ str ++ "'")
                 (\x => case x of
                             Keyword s => if s == str then Just Builtin.MkUnit
                                                      else Nothing
                             _ => Nothing)

  export
  identifier : Rule String
  identifier
    = terminal "Expected Identifier"
               (\x => case x of
                                  ID str => Just str
                                  _ => Nothing)

  export
  name : Rule String
  name = identifier

  export
  ref : Rule Ref
  ref =
    do s <- Toolkit.location
       n <- name
       e <- Toolkit.location
       pure (MkRef (newFC s e) n)


  export
  gives : String -> a -> Rule a
  gives s ctor
    = do keyword s
         pure ctor

  export
  inserts : Rule a -> (a -> b) -> Rule b
  inserts value ctor
    = do v <- value
         pure (ctor v)

  export
  whole : Rule Whole
  whole =
      do n <- nat
         isWhole n
    where
      isWhole : Nat -> RuleEmpty Whole
      isWhole Z = fail "expected whole"
      isWhole (S n) = pure (W (S n) ItIsSucc)

  export
  sFooter : Location -> Rule FileContext
  sFooter s
    = do symbol ")"
         symbol ";"
         e <- Toolkit.location
         pure (newFC s e)

namespace Direction
  export
  direction : Rule Direction
  direction = gives "input" INPUT <|> gives "output" OUTPUT

namespace Types

  mutual
    logic : Rule DType
    logic = gives "logic" LOGIC

    array : Rule DType
    array
        = do ty <- logic
             ns <- indices
             pure (arraytype ty ns)
      where
        index : Rule Whole
        index
          = do symbol "["
               n <- whole
               symbol "]"
               pure n

        indices : Rule (List1 Whole)
        indices = some index

        arraytype : DType -> List1 Whole -> DType
        arraytype ty (x:::xs) = foldl (\ty, n => BVECT n ty) ty (x::xs)

    export
    type : Rule DType
    type = array <|> logic

namespace Kinds

  export
  gateKind : Rule GateKind
  gateKind =  gives "nand" ANDN
          <|> gives "and"  AND
          <|> gives "xor"  XOR
          <|> gives "xnor" XORN
          <|> gives "ior"  IOR
          <|> gives "nior" IORN
          <|> gives "join" JOIN

namespace Terms

  portDecl : Rule (Location, Ref, Direction, DType)
  portDecl
    = do s <- Toolkit.location
         d <- direction
         t <- type
         r <- ref
         pure (s,r,d,t)

  portList : Rule (List1 (Location,Ref, Direction, DType))
  portList
    = do symbol "("
         ps <- sepBy1 (symbol ",") portDecl
         symbol ")"
         symbol ";"
         pure ps

  data Body = WDecl  FileContext DType Ref Ref
            | GInst  FileContext GateKind Ref Ref Ref
            | DInst  FileContext Ref Ref Ref
            | NInst  FileContext Ref Ref
            | MInst  FileContext Ref Ref Ref Ref
            | ISInst FileContext Ref Ref
            | IEInst FileContext End Ref Ref Ref
            | IPInst FileContext Nat Ref Ref Ref Ref

            | ESInst FileContext Ref Ref
            | Merge  FileContext Ref Ref Ref


  gateNot : Rule Body
  gateNot
    = do s <- Toolkit.location
         keyword "not"
         symbol "("
         o <- ref
         symbol ","
         i <- ref
         fc <- sFooter s
         pure (NInst fc o i)

  gateBin : Rule Body
  gateBin
    = do s <- Toolkit.location
         k <- gateKind
         symbol "("
         o <- ref
         symbol ","
         a <- ref
         symbol ","
         b <- ref
         fc <- sFooter s
         e <- Toolkit.location
         pure (GInst fc k o a b)

  gateCopy : Rule Body
  gateCopy
    = do s <- Toolkit.location
         keyword "copy"
         symbol "("
         o <- ref
         symbol ","
         a <- ref
         symbol ","
         b <- ref
         fc <- sFooter s
         pure (DInst fc o a b)

  gateMux : Rule Body
  gateMux
    = do s <- Toolkit.location
         keyword "mux"
         symbol "("
         o <- ref
         symbol ","
         c <- ref
         symbol ","
         a <- ref
         symbol ","
         b <- ref
         fc <- sFooter s
         pure (MInst fc o c a b)

  gateMerge : Rule Body
  gateMerge
    = do s <- Toolkit.location
         keyword "merge"
         symbol "("
         o <- ref
         symbol ","
         a <- ref
         symbol ","
         b <- ref
         fc <- sFooter s
         pure (Merge fc o a b)

  gateSplit : Rule Body
  gateSplit
      = singletonI <|> singletonE <|> edge <|> split
    where

      singletonE : Rule Body
      singletonE
        = do s <- Toolkit.location
             keyword "extract"
             symbol "("
             o <- ref
             symbol ","
             i <- ref
             fc <- sFooter s
             pure (ISInst fc o i)

      singletonI : Rule Body
      singletonI
        = do s <- Toolkit.location
             keyword "insert"
             symbol "("
             o <- ref
             symbol ","
             i <- ref
             fc <- sFooter s
             pure (ESInst fc o i)

      kind : Rule End
      kind = gives "first" F <|> gives "last" L

      edge : Rule Body
      edge
        = do s <- Toolkit.location
             k <- kind
             symbol "("
             a <- ref
             symbol ","
             b <- ref
             symbol ","
             i <- ref
             fc <- sFooter s
             pure (IEInst fc k a b i)

      split : Rule Body
      split
        = do s <- Toolkit.location
             keyword "index"
             symbol "["
             n <- nat
             symbol "]"
             symbol "("
             a <- ref
             symbol ","
             b <- ref
             symbol ","
             x <- ref
             symbol ","
             y <- ref
             fc <- sFooter s
             pure (IPInst fc n a b x y)


  wireDecl : Rule Body
  wireDecl
      = do s <- Toolkit.location
           keyword "wire"
           t <- type
           keyword "as"
           symbol "("
           a <- ref
           symbol ","
           b <- ref
           symbol ")"
           symbol ";"
           e <- Toolkit.location
           pure (WDecl (newFC s e) t a b)

  expr : Rule Body
  expr =  wireDecl
      <|> gateNot
      <|> gateBin
      <|> gateCopy
      <|> gateSplit
      <|> gateMux
      <|> gateSplit
      <|> gateMerge

  foldBody : Location
          -> List Body
          -> AST
  foldBody l Nil
        = Stop (newFC l l)
  foldBody l (head :: tail)
        = foldr doFold (Stop (newFC l l)) (head :: tail)
    where
      doFold : Body -> AST -> AST
      doFold (WDecl x y z w) accum
        = Wire x y z w accum

      doFold (MInst v x y z w) accum
        = Seq (Mux v (Var x) (Var y) (Var z) (Var w))
              accum

      doFold (GInst x k y z w) accum
        = Seq (Gate x k (Var y) (Var z) (Var w))
              accum

      doFold (DInst x y z w) accum
        = Seq (Dup x (Var y) (Var z) (Var w))
              accum

      doFold (NInst x y z) accum
        = Seq (Not x (Var y) (Var z))
              accum

      doFold (ISInst x y z) accum
        = Seq (IndexS x (Var y) (Var z))
              accum

      doFold (IEInst v w x y z) accum
        = Seq (IndexE v w (Var x) (Var y) (Var z))
              accum

      doFold (IPInst u v w x y z) accum
        = Seq (IndexP u v (Var w) (Var x) (Var y) (Var z))
              accum

      doFold (ESInst fc o i) accum
        = Seq (MergeS fc (Var o) (Var i))
              accum

      doFold (Merge fc o a b) accum
        = Seq (MergeV fc (Var o) (Var a) (Var b))
              accum

  foldPorts : Location
           -> List1 (Location,Ref, Direction, DType)
           -> AST
           -> AST
  foldPorts e (x:::xs) y
    = foldr (\(s,r,d,t), body => Input (newFC s e) d t r body) y (x::xs)

  export
  design : Rule AST
  design
    = do keyword "module"
         n <- ref
         ps <- portList
         b <- many expr
         e <- Toolkit.location
         keyword "endmodule"
         symbol ";"
         pure (foldPorts e ps (foldBody e b))

namespace Idealised

  export
  fromFile : (fname : String)
                   -> IO (Either (ParseError Token) AST)
  fromFile fname
    = case !(parseFile Idealised.Lexer design fname) of
        Left err  => pure (Left err)
        Right ast => pure (Right (setSource fname ast))
-- [ EOF ]
