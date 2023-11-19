{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

module Main where

import Choreography
import Choreography.Choreo
import Choreography.Location

import Data.Proxy
import Data.Time
import System.Environment
import GHC.TypeLits
import Control.Monad.Identity (Identity(..), runIdentity)
import "freer-simple" Control.Monad.Freer as S
import "HasChor" Control.Monad.Freer (interpFreer, toFreer)

import Flame.Principals
import Flame.TCB.Freer.IFC

type Buyer = N "buyer"
buyer :: SPrin Buyer
buyer = SName (Proxy :: Proxy "buyer")

type Seller = N "seller"
seller :: SPrin Seller
seller = SName (Proxy :: Proxy "seller")

type BS = (Buyer \/ Seller)

bs :: SPrin BS
bs = (buyer *\/ seller)

type FromBuyer = ((C (Buyer \/ Seller)) /\ (I Buyer))
fromBuyer :: SPrin FromBuyer
fromBuyer = (((buyer *\/ seller)*->) */\ (buyer*<-))

type FromSeller = ((C (Buyer \/ Seller)) /\ (I Seller))
fromSeller :: SPrin FromSeller
fromSeller = (((buyer *\/ seller)*->) */\ (seller*<-))

label_in :: l!(a @ loc) -> (l!a) @ loc
label_in lal = wrap $ bind lal (label . unwrap)

-- label_out :: (l!a) @ loc -> l!(a @ loc) 
-- label_out lal = bind (unwrap lal) (label . wrap)

join_in :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> (l''!a) @ loc
join_in = wrap . join . unwrap . label_in

join_out :: (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> l''!(a @ loc)
join_out llal = bind llal (\lal -> bind (unwrap lal) $ label . wrap)

-- | Perform a local computation at a given location.
s_locally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l!a))
               -> Labeled (Choreo m) pc ((l!a) @ loc)
s_locally (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) $ (\un -> runLabeled $ k un))
  return $ label_in (join_out @pc @l result)

(~>:) :: (Show a, Read a, KnownSymbol loc, KnownSymbol loc', (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  -- ^ A triple of a sender's location, a clearance, 
                                           -- and a value located
                                           -- at the sender
     -> Proxy loc'                           -- ^ A receiver's location.
     -> Labeled (Choreo m) pc ((pc!(l!a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <- restrict pc (\_ -> ((loc, la) ~> loc'))
  return $ label_in result

-- | Conditionally execute choreographies based on a located value.
s_cond :: (Show a, Read a, KnownSymbol l)
     => (Proxy l, SPrin pc, (a @ l)) -- ^ A pair of a location and a scrutinee located on
                                         -- it.
     -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Labeled (Choreo m) pc (pc!b)
s_cond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (\la -> runLabeled $ c la)

s_putStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
s_putStrLn pc la = restrict pc (\open -> putStrLn (show $ open la))

s_getLine :: SPrin pc -> Labeled IO pc (pc!String)
s_getLine pc = restrict pc (\_ -> getLine)

safe_putStrLn :: (Show a, l ⊑ BS) => l!a 
                      -> Labeled IO BS (BS!())
safe_putStrLn =  s_putStrLn bs

buyer_getLine :: Labeled IO FromBuyer (FromBuyer!String)
buyer_getLine = s_getLine fromBuyer

-- | `bookseller` is a choreography that implements the bookseller protocol.
bookseller :: Labeled (Choreo IO) BS ((FromBuyer ! Maybe Day) @ "buyer")
bookseller = do
  -- the buyer node prompts the user to enter the title of the book to buy
  title <- (bs, buyer, bs, fromBuyer) `s_locally` \_ -> do
             safe_putStrLn $ label "Enter the title of the book to buy"
             relabel' bs buyer_getLine

  -- the buyer sends the title to the seller
  title' <- (sym buyer, bs, fromBuyer, title) ~>: sym seller
  return title'
 
  -- the seller checks the price of the book
  price <- (bs, seller, bs, fromSeller) `s_locally` \un -> do
    use (join (un title')) (\t -> protect $ priceOf t)
  -- the seller sends back the price of the book to the buyer
  price' <- (sym seller, bs, fromSeller, price) ~>: sym buyer
 
  -- the buyer decides whether to buy the book or not
  decision <- (bs, buyer, bs, fromBuyer) `s_locally` \un -> do
    use (join (un price')) (\p -> protect (p < budget))
 
  -- if the buyer decides to buy the book, the seller sends the delivery date to the buyer
  -- TODO: needs some label/loc manipulation...(join_in $ 
  s_cond (sym buyer, bs, decision) $ \d -> use d \case
    True  -> do
      deliveryDate  <- (bs, seller, bs, fromSeller) `s_locally` \un -> do
        use (join (un title')) (\t -> protect $ deliveryDateOf t)
      deliveryDate' <- (sym seller, bs, fromSeller, price) ~>: sym buyer
 
      (bs, buyer, bs, fromBuyer) `s_locally` \un -> do
        use (join (un deliveryDate')) 
          (\dd -> 
            safe_putStrLn $ label ("The book will be delivered on " ++ show dd)
            label $ Just dd)
 
    False -> do
      (bs, buyer, bs, fromBuyer) `s_locally` \un -> do
        safe_putStrLn $ label "The book's price is out of the budget"
        label $ Nothing

{- 
---- `bookseller'` is a simplified version of `bookseller` that utilizes `~~>`
--bookseller' :: Choreo IO (Maybe Day @ "buyer")
--bookseller' = do
--  title <- (buyer, \_ -> do
--               putStrLn "Enter the title of the book to buy"
--               getLine
--           )
--           ~~> seller
--
--  price <- (sym seller, \un -> return $ priceOf (un title)) ~~> (sym buyer)
--
--  cond' (sym buyer, \un -> return $ (un price) < budget) \case
--    True  -> do
--      deliveryDate <- (sym seller, \un -> return $ deliveryDateOf (un title)) ~~> (sym buyer)
--
--      (sym buyer) `locally` \un -> do
--        putStrLn $ "The book will be delivered on " ++ show (un deliveryDate)
--        return $ Just (un deliveryDate)
--
--    False -> do
--      (sym buyer) `locally` \_ -> do
--        putStrLn "The book's price is out of the budget"
--        return Nothing
-}

budget :: Int
budget = 100

priceOf :: String -> Int
priceOf "Types and Programming Languages" = 80
priceOf "Homotopy Type Theory"            = 120

deliveryDateOf :: String -> Day
deliveryDateOf "Types and Programming Languages" = fromGregorian 2022 12 19
deliveryDateOf "Homotopy Type Theory"            = fromGregorian 2023 01 01

main :: IO ()
main = do
  [loc] <- getArgs
  case loc of
    "buyer"  -> runChoreography cfg (runLabeled bookseller) "buyer"
    "seller" -> runChoreography cfg (runLabeled bookseller) "seller"
  return ()
  where
    cfg = mkHttpConfig [ ("buyer",  ("localhost", 4242))
                       , ("seller", ("localhost", 4343))
                       ]

--main :: IO ()
---main = undefined