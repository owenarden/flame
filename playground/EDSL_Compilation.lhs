---
title: Compilation as a Typed EDSL-to-EDSL Transformation
author: Emil Axelsson
colorlinks: blue
link-citations: true
header-includes:
include-before:
---


  <style type="text/css">
body {
  font-family: sans-serif;
  font-size: 95%;
  max-width: 50em;
}

div#header {
  text-align: center;
}

h1 {
  font-size: 130%;
  margin-top: 2em;
  border-bottom: 1px solid grey;
}

h2 {
  font-size: 105%;
  margin-top: 1.5em;
}

h3 {
  font-size: 98%;
}

h1.title {
  font-size: 180%;
  margin-top: 0.5em;
  border-bottom: none;
}

h2.author {
  font-size: 120%;
}

h3.date {
  font-size: 120%;
}

span.header-section-number {
  margin-right: 1em;
}

pre { background-color: #E5E5E5; }
pre > code { background-color: #E5E5E5; }
  /* `#E5E5E5` chosen because Blogger seems to dynamically change the
     `pre > code` color to this. Originally I wanted `#EEE`, but then I got
     slightly different shades for the color under characters in code, and the
     background of the code block, the latter being set to `#E5E5E5`.
  */
  </style>



Abstract
================================================================================

This article is about an implementation and compilation technique that is used in [RAW-Feldspar](https://github.com/emilaxelsson/raw-feldspar/tree/article-2016-03) which is a complete rewrite of the Feldspar embedded domain-specific language (EDSL) [@axelsson2010feldspar]. Feldspar is high-level functional language that generates efficient C code to run on embedded targets.

The gist of the technique presented in this post is the following: rather writing a back end that converts pure Feldspar expressions directly to C, we translate them to a low-level monadic EDSL. From the low-level EDSL, C code is then generated.

This approach has several advantages:

  1. The translation is simpler to write than a complete C back end.
  2. The translation is between two typed EDSLs, which rules out many potential errors.
  3. The low-level EDSL is reusable and can be shared between several high-level EDSLs.

Although the article contains a lot of code, most of it is in fact reusable. As mentioned in [Discussion], we can write the same implementation in less than 50 lines of code using generic libraries that we have developed to support Feldspar.



Introduction
================================================================================

There has been a recent trend to implement low-level imperative EDSLs based on monads [@persson2012generic; @svenningsson2013simple; @hickey2014building; @bracker2014sunroof]. By using a deep embedding of monadic programs, imperative EDSL code can be translated directly to corresponding code in the back end (e.g. C or JavaScript code).

A deep embedding of a monad with primitive instruction gives a representation of the statements of an imperative language. But in order for a language to be useful, there also needs to be a notion of pure expressions. Take the following program as example:

~~~~~~~~~~~~~~~~~~~~{.haskell}
prog = do
    i <- readInput
    writeOutput (i+i)
~~~~~~~~~~~~~~~~~~~~

In order to generate code from this program we need a representation of the whole syntax, including the expression `i+i`. And it is usually not enough to support such simple expressions. For example, in RAW-Feldspar, we can write the following,

~~~~~~~~~~~~~~~~~~~~{.haskell}
prog = do
    i <- fget stdin
    printf "sum: %d\n" $ sum $ map square (0 ... i)
  where
    square x = x*x
~~~~~~~~~~~~~~~~~~~~

and have it generate this C code:

~~~~~~~~~~~~~~~~~~~~{.c}
 #include <stdint.h>
 #include <stdio.h>
int main()
{
    uint32_t v0;
    uint32_t let1;
    uint32_t state2;
    uint32_t v3;

    fscanf(stdin, "%u", &v0);
    let1 = v0 + 1;
    state2 = 0;
    for (v3 = 0; v3 < (uint32_t) (0 < let1) * let1; v3++) {
        state2 = v3 * v3 + state2;
    }
    fprintf(stdout, "sum: %d\n", state2);
    return 0;
}
~~~~~~~~~~~~~~~~~~~~

Note that the pure expression `sum $ map square (0 ... i)` was turned into several statements in the C code (everything from `let1 =` to the end of the loop). What happened here was that `sum $ map square (0 ... i)` was first transformed to a more low-level (but still pure) expression that involves a let binding and a looping construct. This expression was then translated to C code.

However, the story is actually more interesting than that: Instead of translating the pure expression directly to C, which can be a tedious and error-prone task, it is first translated to a typed low-level EDSL that only has simple expressions and a straightforward translation to C. Going through a typed EDSL makes the translation simple and robust, and this low-level EDSL has the advantage of being generic and reusable between different high-level EDSLs.

This post will show a simplified version of the technique used in RAW-Feldspar. For the full story, see the RAW-Feldspar implementation (tag [article-2016-03](https://github.com/emilaxelsson/raw-feldspar/tree/article-2016-03)). The low-level EDSL that is used for compiling Feldspar to C is provided by the package [imperative-edsl](http://hackage.haskell.org/package/imperative-edsl-0.5).



Outline of the technique
================================================================================

Our technique is based on a deep monadic embedding of imperative programs:

~~~~~~~~~~~~~~~~~~~~{.haskell}
data Prog exp a where ...

instance Monad (Prog exp)
~~~~~~~~~~~~~~~~~~~~

By parameterizing `Prog` on the expression type `exp`, we can have imperative programs with different representations of expressions.

Next, we define two expression languages:

~~~~~~~~~~~~~~~~~~~~{.haskell}
data LowExp a  where ...
data HighExp a where ...
~~~~~~~~~~~~~~~~~~~~

`LowExp` is a simple language containing only variables, literals, operators and function calls. `HighExp` is a richer language that may contain things like let binding, tuples and pure looping constructs.

Since `LowExp` is so simple, we can easily -- once and for all -- write a back end that translates `Prog LowExp` to C code:

~~~~~~~~~~~~~~~~~~~~{.haskell}
lowToCode :: Prog LowExp a -> String
~~~~~~~~~~~~~~~~~~~~

Once this is done, we can implement the compiler for `HighExp` simply as a typed translation function between two EDSLs:

~~~~~~~~~~~~~~~~~~~~{.haskell}
translateHigh :: Prog HighExp a -> Prog LowExp a

compile :: Prog HighExp a -> String
compile = lowToCode . translateHigh
~~~~~~~~~~~~~~~~~~~~

If we want to make changes to `HighExp`, we only need to update the `translateHigh` function. And if we want to implement an EDSL with a different expression language, we simply write a different translation function for that language.



A deep embedding of imperative programs
================================================================================

The code is available as a [literate Haskell file](https://gist.github.com/emilaxelsson/ddcc352b7422fe763c70#file-edsl_compilation-lhs).

We make use of the following GHC extensions:

\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
\end{code}

  <!--
\begin{code}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module EDSL_Compilation where

import Language.Embedded.Backend.C.Expression (CType)
\end{code}
  -->

And we also need a few helper modules:

\begin{code}
import Control.Monad.State
import Control.Monad.Writer
import Data.Int
import Data.IORef
\end{code}

We are now ready to define our monadic deep embedding. Our EDSL will be centered around the monad `Prog` (inspired by the `Program` monad in [Operational](http://hackage.haskell.org/package/operational) and the work of @svenningsson2013simple):

\begin{code}
data Prog exp a where
  Return :: a -> Prog exp a
  (:>>=) :: Prog exp a -> (a -> Prog exp b) -> Prog exp b
  CMD    :: CMD exp a -> Prog exp a

instance Functor (Prog exp) where
  fmap f m = m >>= return . f

instance Applicative (Prog exp) where
  pure  = return
  (<*>) = ap

instance Monad (Prog exp) where
  return = Return
  (>>=)  = (:>>=)
\end{code}

As seen in the `Monad` instance, `Return` and `(:>>=)` directly represent uses of `return` and `(>>=)`, respectively. `CMD` injects a primitive instruction from the type `CMD a` which will be defined below.

The attentive reader may react that `Prog` actually does not satisfy the monad laws, since it allows us to observe the nesting of `(>>=)` in a program. This is, however, not a problem in practice: we will only interpret `Prog` in ways that are ignorant of the nesting of `(>>=)`.

(The [Operational](http://hackage.haskell.org/package/operational) package honors the monad laws by only providing an abstract interface to `Program`, preventing interpretations that would otherwise be able to observe the nesting of `(>>=)`.)



Primitive instructions
----------------------------------------

The `CMD` type contains the primitive instructions of the EDSL. It has instructions for mutable references, input/output and loops:

\begin{code}
data CMD exp a where
  -- References:
  InitRef :: Type a => exp a -> CMD exp (Ref a)
  GetRef  :: Type a => Ref a -> CMD exp (Val a)
  SetRef  :: Type a => Ref a -> exp a -> CMD exp ()

  -- Input/output:
  Read     :: CMD exp (Val Int32)
  Write    :: exp Int32 -> CMD exp ()
  PrintStr :: String -> CMD exp ()

  -- Loops:
  For :: exp Int32 -> (Val Int32 -> Prog exp ()) -> CMD exp ()
\end{code}

The instructions `InitRef`, `GetRef` and `SetRef` correspond to `newIORef`, `readIORef` and `writeIORef` from `Data.IORef`.

`Read` and `Write` are used to read integers from `stdin` and write integers to `stdout`. `PrintStr` prints a static string to `stdout`.

`For n body` represents a for-loop of `n` iterations, where `body` gives the program to run in each iteration. The argument to `body` ranges from 0 to `n`-1.

As explained in [Outline of the technique], `exp` represents pure expressions, and we have it as a parameter in order to be able to use the same instructions with different expression types.

Now we have three things left to explain: `Type`, `Val` and `Ref`.

The `Type` class is just used to restrict the set of types that can be used in our EDSL. For simplicity, we will go with the following class

  <!--
\begin{code}
class    (Eq a, Ord a, Show a, CType a) => Type a
instance (Eq a, Ord a, Show a, CType a) => Type a
\end{code}

Not showing this code, because `CType` is actually not used in the article. It is only needed to allow `UnsingImperativeEDSL.hs` to import this module unchanged.

  -->

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.haskell}
class    (Eq a, Ord a, Show a) => Type a
instance (Eq a, Ord a, Show a) => Type a
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

`Val` is used whenever an instruction produces a pure value (e.g. `GetRef`). It would make sense to use `exp a` instead of `Val a`. However, that would lead to problems later when we want to translate between different expression types. We can think of `Val a` as representing a value in *any expression type*.

In order to interpret a program, we must have concrete representations of the types returned by the primitive instructions. For example, interpreting the program `CMD Read :>>= \a -> ...`, requires creating an actual value of type `Val Int32` to pass to the continuation. However, depending on the interpretation, we may need different representations for this value.

In a standard interpretation (e.g. running the program in Haskell's `IO` monad), we want `Val a` to be represented by an actual value of type `a`. But in a non-standard interpretation such as compilation to C code, we want `Val a` to be a variable identifier. To reconcile these different needs, we define `Val` as a sum type:

\begin{code}
data Val a
  = ValRun a       -- Concrete value
  | ValComp VarId  -- Symbolic value

-- Variable identifier
type VarId = String
\end{code}

For the same reason, `Ref` is defined to be either an actual `IORef` or a variable identifier:

\begin{code}
data Ref a
  = RefRun (IORef a)  -- Concrete reference
  | RefComp VarId     -- Symbolic reference
\end{code}

Unfortunately, having sum types means that our interpretations will sometimes have to do incomplete pattern matching. For example, the standard interpretation of `GetRef r` will assume that `r` is a `RefRun` (a variable identifier has no meaning in the standard interpretation), while the interpretation that compiles to C will assume that it is a `RefComp`. However, the EDSL user is shielded from this unsafety. By making `Val` and `Ref` abstract types, we ensure that users' programs are unaware of the interpretation which is applied to them. As long as our interpreters are correct, no-one will suffer from the unsafety due to `Val` and `Ref` being sum types.



Interpretation
----------------------------------------

The following function lifts an interpretation of instructions in a monad `m` to an interpretation of programs in the same monad (corresponding to `interpretWithMonad` in [Operational](http://hackage.haskell.org/package/operational)):

\begin{code}
interpret :: Monad m
          => (forall a . CMD exp a -> m a)
          -> Prog exp a -> m a
interpret int (Return a) = return a
interpret int (p :>>= k) = interpret int p >>= interpret int . k
interpret int (CMD cmd)  = int cmd
\end{code}

Using `interpret`, we can define the standard interpretation that runs a program in the `IO` monad:

\begin{code}
runIO :: EvalExp exp => Prog exp a -> IO a
runIO = interpret runCMD

runCMD :: EvalExp exp => CMD exp a -> IO a
runCMD (InitRef a)           = RefRun <$> newIORef (evalExp a)
runCMD (GetRef (RefRun r))   = ValRun <$> readIORef r
runCMD (SetRef (RefRun r) a) = writeIORef r (evalExp a)
runCMD Read                  = ValRun . read <$> getLine
runCMD (Write a)             = putStr $ show $ evalExp a
runCMD (PrintStr s)          = putStr s
runCMD (For n body)          =
    mapM_ (runIO . body . ValRun) [0 .. evalExp n - 1]
\end{code}

Most of the work is done in `runCMD` which gives the interpretation of each instruction. Note the use of `ValRun` and `RefRun` on both sides of the equations. As said earlier, `ValComp` and `RefComp` are not used in the standard interpretation.

Since running a program also involves evaluating expressions, we need the constraint `EvalExp exp` that gives access to the function `evalExp` (for example in the interpretation of `InitRef`). `EvalExp` is defined as follows:

\begin{code}
class EvalExp exp where
  -- Evaluate a closed expression
  evalExp :: exp a -> a
\end{code}



Front end
----------------------------------------

We are now ready to define the smart constructors that we will give as the interface to the EDSL user. For many instructions, the smart constructor just takes care of lifting it to a program using `CMD`, for example:

\begin{code}
initRef :: Type a => exp a -> Prog exp (Ref a)
initRef = CMD . InitRef

setRef :: Type a => Ref a -> exp a -> Prog exp ()
setRef r a = CMD (SetRef r a)
\end{code}

But instructions that involve `Val` will need more care. We do not actually want to expose `Val` to the user, but rather use `exp` to hold values. To achieve this, we introduce a class for expressions supporting injection of constants and variables:

\begin{code}
class FreeExp exp where
  -- Inject a constant value
  constExp :: Type a => a -> exp a

  -- Inject a variable
  varExp   :: Type a => VarId -> exp a
\end{code}

Using `FreeExp`, we can make a general function that converts `Val` to an expression -- independent of interpretation:

\begin{code}
valToExp :: (Type a, FreeExp exp) => Val a -> exp a
valToExp (ValRun a)  = constExp a
valToExp (ValComp v) = varExp v
\end{code}

Now we can define the rest of the front end, using `valToExp` where needed:

\begin{code}
getRef :: (Type a, FreeExp exp) => Ref a -> Prog exp (exp a)
getRef = fmap valToExp . CMD . GetRef

readInput :: FreeExp exp => Prog exp (exp Int32)
readInput = valToExp <$> CMD Read

writeOutput :: exp Int32 -> Prog exp ()
writeOutput = CMD . Write

printStr :: String -> Prog exp ()
printStr = CMD . PrintStr

for :: FreeExp exp
    => exp Int32 -> (exp Int32 -> Prog exp ()) -> Prog exp ()
for n body = CMD $ For n (body . valToExp)
\end{code}

As a convenience, we also provide a function for modifying a reference using a pure function:

\begin{code}
modifyRef :: (Type a, FreeExp exp)
          => Ref a -> (exp a -> exp a) -> Prog exp ()
modifyRef r f = setRef r . f =<< getRef r
\end{code}



Pure expressions
================================================================================

Now that we have a front end for the imperative EDSL, we also need to define an expression type before we can use it for anything.

We begin with a very simple expression type that only has variables, literals and some primitive functions:

\begin{code}
data LowExp a where
  LVar :: Type a => VarId -> LowExp a
  LLit :: Type a => a -> LowExp a
  LAdd :: (Num a, Type a) => LowExp a -> LowExp a -> LowExp a
  LMul :: (Num a, Type a) => LowExp a -> LowExp a -> LowExp a
  LNot :: LowExp Bool -> LowExp Bool
  LEq  :: Type a => LowExp a -> LowExp a -> LowExp Bool
\end{code}

As common in Haskell EDSLs, we provide a `Num` instance to make it easier to construct expressions:

\begin{code}
instance (Num a, Type a) => Num (LowExp a) where
  fromInteger = LLit . fromInteger
  (+) = LAdd
  (*) = LMul
\end{code}

This instance allows us to write things like `5+6 :: LowExp Int32`.

The implementation of `LowExp` is completed by instantiating the `EvalExp` and `FreeExp` classes:

\begin{code}
instance EvalExp LowExp where
  evalExp (LLit a)   = a
  evalExp (LAdd a b) = evalExp a + evalExp b
  evalExp (LMul a b) = evalExp a * evalExp b
  evalExp (LNot a)   = not $ evalExp a
  evalExp (LEq a b)  = evalExp a == evalExp b

instance FreeExp LowExp where
  constExp = LLit
  varExp   = LVar
\end{code}



First example
----------------------------------------

We can now write our first imperative example program:

\begin{code}
sumInput :: Prog LowExp ()
sumInput = do
  r <- initRef 0
  printStr "Please enter 4 numbers\n"
  for 4 $ \i -> do
    printStr " > "
    n <- readInput
    modifyRef r (+n)
  printStr "The sum of your numbers is "
  s <- getRef r
  writeOutput s
  printStr ".\n"
\end{code}

This program uses a for-loop to read four number from the user. It keeps the running sum in a reference, and prints the final sum before quitting. An example run can look as follows:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
*EDSL_Compilation> runIO sumInput
Please enter 4 numbers
 > 1
 > 2
 > 3
 > 4
The sum of your numbers is 10.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Code generation
----------------------------------------

The code generator is defined using `interpret` with the target being a code generation monad `Code`:

\begin{code}
code :: ShowExp exp => Prog exp a -> Code a
code = interpret codeCMD

lowToCode :: Prog LowExp a -> String
lowToCode = runCode . code
\end{code}

The definition of `codeCMD` is deferred to [Appendix: Code generation].

In this article, the code generator only produces simple imperative pseudo-code. Here is the code generated from the `sumInput` example:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
*EDSL_Compilation> putStrLn $ lowToCode sumInput
    r0 <- initRef 0
    readInput "Please enter 4 numbers\n"
    for v1 < 4
        readInput " > "
        v2 <- stdin
        v3 <- getRef r0
        setRef r0 (v3 + v2)
    end for
    readInput "The sum of your numbers is "
    v4 <- getRef r0
    writeOutput v4
    readInput ".\n"
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



High-level expressions
================================================================================

The expression language `LowExp` is really too simple to be very useful. For example, it does not allow any kind of iteration, so any iterative program has to be written using the monadic for-loop.

To fix this, we introduce a new expression language, `HighExp`:

\begin{code}
data HighExp a where
  -- Simple constructs (same as in LowExp):
  HVar :: Type a => VarId -> HighExp a
  HLit :: Type a => a -> HighExp a
  HAdd :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HMul :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HNot :: HighExp Bool -> HighExp Bool
  HEq  :: Type a => HighExp a -> HighExp a -> HighExp Bool

  -- Let binding:
  Let  :: Type a
       => HighExp a                 -- value to share
       -> (HighExp a -> HighExp b)  -- body
       -> HighExp b

  -- Pure iteration:
  Iter :: Type s
       => HighExp Int32            -- number of iterations
       -> HighExp s                -- initial state
       -> (HighExp s -> HighExp s) -- step function
       -> HighExp s                -- final state

instance (Num a, Type a) => Num (HighExp a) where
  fromInteger = HLit . fromInteger
  (+) = HAdd
  (*) = HMul

instance FreeExp HighExp where
  constExp = HLit
  varExp   = HVar
\end{code}

`HighExp` contains the same simple constructs as `LowExp`, but has been extended with two new constructs: let binding and iteration. Both of these constructs use higher-order abstract syntax (HOAS) [@pfenning1988higher] as a convenient way to introduce local variables.

The following program uses `HighExp` to represent expressions:

\begin{code}
powerInput :: Prog HighExp ()
powerInput = do
  printStr "Please enter two numbers\n"
  printStr " > "; m <- readInput
  printStr " > "; n <- readInput
  printStr "Here's a fact: "
  writeOutput m; printStr "^"; writeOutput n; printStr " = "
  writeOutput $ Iter n 1 (*m)
  printStr ".\n"
\end{code}

It asks the user to input two numbers `m` and `n`, and and prints the result of `m^n`. Note the use of `Iter` to compute `m^n` as a pure expression.



Compilation as a typed EDSL translation
================================================================================

Now we are getting close to the main point of the article. This is what we have so far:

  * A way to generate code from low-level programs (of type `Prog LowExp a`).
  * The ability to write high-level programs (of type `Prog HighExp a`).

What is missing is a function that translates high-level programs to low-level programs. Generalizing the problem a bit, we need a way to rewrite a program over one expression type to a program over a different expression type -- a process which we call "re-expressing".

Since `Prog` is a monad like any other, we can actually express this translation function using `interpret`:

\begin{code}
reexpress :: (forall a . exp1 a -> Prog exp2 (exp2 a))
          -> Prog exp1 b
          -> Prog exp2 b
reexpress reexp = interpret (reexpressCMD reexp)

reexpressCMD :: (forall a . exp1 a -> Prog exp2 (exp2 a))
             -> CMD exp1 b
             -> Prog exp2 b
reexpressCMD reexp (InitRef a)  = CMD . InitRef =<< reexp a
reexpressCMD reexp (GetRef r)   = CMD (GetRef r)
reexpressCMD reexp (SetRef r a) = CMD . SetRef r =<< reexp a
reexpressCMD reexp Read         = CMD Read
reexpressCMD reexp (Write a)    = CMD . Write =<< reexp a
reexpressCMD reexp (PrintStr s) = CMD (PrintStr s)
reexpressCMD reexp (For n body) = do
    n' <- reexp n
    CMD $ For n' (reexpress reexp . body)
\end{code}

The first argument to `reexpress` translates an expression in the source language to an expression in the target language. Note the type of this function: `exp1 a -> Prog exp2 (exp2 a)`. Having a monadic result type means that source expressions do not have to be mapped directly to corresponding target expressions -- they can also generate imperative code!

The ability to generate imperative code from expressions is crucial. Consider the `Iter` construct. Since there is no corresponding construct in `LowExp`, the only way we can translate this construct is by generating an imperative for-loop.



Translation of `HighExp`
----------------------------------------

Now that we have a general way to "re-rexpress" programs, we need to define the function that translates `HighExp` to `LowExp`. The first cases just map `HighExp` constructs to their corresponding `LowExp` constructs:

\begin{code}
transHighExp :: HighExp a -> Prog LowExp (LowExp a)
transHighExp (HVar v)   = return (LVar v)
transHighExp (HLit a)   = return (LLit a)
transHighExp (HAdd a b) = LAdd <$> transHighExp a <*> transHighExp b
transHighExp (HMul a b) = LMul <$> transHighExp a <*> transHighExp b
transHighExp (HNot a)   = LNot <$> transHighExp a
transHighExp (HEq a b)  = LEq  <$> transHighExp a <*> transHighExp b
\end{code}

It gets more interesting when we get to `Let`. There is no corresponding construct in `LowExp`, so we have to realize it using imperative constructs:

\begin{code}
transHighExp (Let a body) = do
  r  <- initRef =<< transHighExp a
  a' <- CMD $ GetRef r
  transHighExp $ body $ valToExp a'
\end{code}

The shared value `a` must be passed to `body` *by-value*. This is achieved by initializing a reference with the value of `a` and immediately reading out that value. Note that we cannot use the smart constructor `getRef` here, because it would return an expression of type `LowExp` while `body` expects a `HighExp` argument. By using `CMD $ GetRef r`, we obtain a result of type `Val`, which can be translated to any expression type using `valToExp`.

 > ***Exercise:** Change the translation of `Let` to use call-by-name semantics instead.*

Translation of `Iter` is similar to that of `Let` in that it uses a reference for the local state. The iteration is realized by an imperative `for` loop. In each iteration, the state variable `r` is read, then the next state is computed and written back to the `r`. After the loop, the content of `r` is returned as the final state.

\begin{code}
transHighExp (Iter n s body) = do
  n' <- transHighExp n
  r  <- initRef =<< transHighExp s
  for n' $ \_ -> do
    sPrev <- CMD $ GetRef r
    sNext <- transHighExp $ body $ valToExp sPrev
    setRef r sNext
  getRef r
\end{code}

 > ***Exercise:** Change the translation of `Iter` by unrolling the body twice when the number of iterations is known to be a multiple of 2:*
 >
 > ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~{.haskell}
 > transHighExp (Iter (HMul n (HLit 2)) s body) = do
 >   ...
 > ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  <!--
Solutions:

\begin{code}
transHighExp' :: HighExp a -> Prog LowExp (LowExp a)

-- Call-by-name:
transHighExp' (Let a body) = transHighExp $ body a

-- Unrolling Iter:
transHighExp' (Iter (HMul n (HLit 2)) s body) = do
  n' <- transHighExp n
  r  <- initRef =<< transHighExp s
  for n' $ \_ -> do
    sPrev <- CMD $ GetRef r
    s1 <- transHighExp $ body $ valToExp sPrev
    setRef r s1
    s1' <- CMD $ GetRef r
    s2 <- transHighExp $ body $ valToExp s1'
    setRef r s2
  getRef r
\end{code}
  -->


All that is left now is to put the pieces together and define the `compile` function:

\begin{code}
translateHigh :: Prog HighExp a -> Prog LowExp a
translateHigh = reexpress transHighExp

compile :: Prog HighExp a -> String
compile = lowToCode . translateHigh
\end{code}

To see that it works as expected, we compile the `powerInput` example:

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
*EDSL_Compilation> putStrLn $ compile powerInput
    printStr "Please enter two numbers\n"
    printStr " > "
    v0 <- readInput
    printStr " > "
    v1 <- readInput
    printStr "Here's a fact: "
    writeOutput v0
    printStr "^"
    writeOutput v1
    printStr " = "
    r2 <- initRef 1
    for v3 < v1
        v4 <- getRef r2
        setRef r2 (v4 * v0)
    end for
    v5 <- getRef r2
    writeOutput v5
    printStr ".\n"
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Note especially the for-loop resulting from the pure expression `Iter n 1 (*m)`.



Discussion
================================================================================

The simplicity of the presented technique can be seen by the fact that *most of the code is reusable*.

  * `Prog`, `interpret` and `reexpress` are independent of the expression language.
  * `LowExp` and its associated functions can be used as target for many different high-level languages.

The only (non-trivial) parts that are not reusable are `HighExp` and `transHighExp`. This shows that in fact very little work is needed to define an EDSL complete with code generation.



Generalized implementation
----------------------------------------

In fact, most of the code presented in this article is available in generic libraries:

  * `Prog`, `interpret` and `reexpress` are available in [operational-alacarte](http://hackage.haskell.org/package/operational-alacarte-0.2) (under the names `Program`, `interpretWithMonad` and `reexpress`).
  * Variants of the instructions in `CMD` are available as separate composable types in the package [imperative-edsl](http://hackage.haskell.org/package/imperative-edsl-0.5) (which, in turn, depends on [operational-alacarte](http://hackage.haskell.org/package/operational-alacarte-0.2)).

As a proof of concept, we provide a [supplementary file](https://gist.github.com/emilaxelsson/ddcc352b7422fe763c70#file-usingimperativeedsl-hs) that implements the `HighExp` compiler using the generic libraries.

The whole compiler, not counting imports and the definition of `HighExp`, is just 30 lines of code! What is more, it emits real *runnable C* code instead of the pseudo-code used in this article.



Richer high-level languages
----------------------------------------

Part of the reason why `transHighExp` was so easy to define is that `HighExp` and `LowExp` support the same set of types. Things get more complicated if we want to extend `HighExp` with, for example, tuples.

Readers interested in how to implement more complex expressions using the presented technique are referred to the RAW-Feldspar source code (tag [article-2016-03](https://github.com/emilaxelsson/raw-feldspar/tree/article-2016-03)).



\newpage

Appendix: Code generation
================================================================================

Here we define he missing parts of the code generator introduced in [Code generation].



Code generation of instructions
----------------------------------------

\begin{code}
-- Code generation monad
type Code = WriterT [Stmt] (State Unique)

type Stmt   = String
type Unique = Integer

runCode :: Code a -> String
runCode = unlines . flip evalState 0 . execWriterT . indent

-- Emit a statement in the generated code
stmt :: Stmt -> Code ()
stmt s = tell [s]

-- Generate a unique identifier
unique :: String -> Code VarId
unique base = do
  u <- get; put (u+1)
  return (base ++ show u)

-- Generate a unique symbolic value
freshVar :: Type a => Code (Val a)
freshVar = ValComp <$> unique "v"

-- Generate a unique reference
freshRef :: Type a => Code (Ref a)
freshRef = RefComp <$> unique "r"

-- Modify a code generator by indenting the generated code
indent :: Code a -> Code a
indent = censor $ map ("    " ++)

-- Code generation of instructions
codeCMD :: ShowExp exp => CMD exp a -> Code a
codeCMD (InitRef a) = do
  r <- freshRef
  stmt $ unwords [show r, "<- initRef", showExp a]
  return r
codeCMD (GetRef r) = do
  v <- freshVar
  stmt $ unwords [show v, "<- getRef", show r]
  return v
codeCMD (SetRef r a) = stmt $ unwords ["setRef", show r, showExp a]
codeCMD Read = do
  v <- freshVar
  stmt $ unwords [show v, "<- readInput"]
  return v
codeCMD (Write a)    = stmt $ unwords ["writeOutput", showExp a]
codeCMD (PrintStr s) = stmt $ unwords ["printStr", show s]
codeCMD (For n body) = do
  i <- freshVar
  stmt $ unwords ["for", show i, "<", showExp n]
  indent $ code (body i)
  stmt "end for"
\end{code}



Showing expressions
----------------------------------------

\begin{code}
instance Show (Val a) where show (ValComp a) = a
instance Show (Ref a) where show (RefComp r) = r

class ShowExp exp where
  showExp :: exp a -> String

bracket :: String -> String
bracket s = "(" ++ s ++ ")"

instance ShowExp LowExp where
  showExp (LVar v)   = v
  showExp (LLit a)   = show a
  showExp (LAdd a b) = bracket (showExp a ++ " + " ++ showExp b)
  showExp (LMul a b) = bracket (showExp a ++ " * " ++ showExp b)
  showExp (LNot a)   = bracket ("not " ++ showExp a)
  showExp (LEq a b)  = bracket (showExp a ++ " == " ++ showExp b)
\end{code}



\newpage

Acknowledgement
================================================================================

This work is funded by the Swedish Foundation for Strategic Research, under grant RAWFP.



References
================================================================================

