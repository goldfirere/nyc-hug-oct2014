{- An example showing units of measure for currency conversion.
   Copyright (c) 2014 Richard Eisenberg
  -}

{-# LANGUAGE TemplateHaskell, TypeFamilies, ExistentialQuantification,
             TypeOperators, DataKinds, ConstraintKinds #-}

module Currencies where

import Data.Metrology
import Data.Metrology.TH

import Text.Read ( readMaybe )
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Network.HTTP
import Data.List.Split

declareMonoUnit "USD" (Just "USD")
declareMonoUnit "EUR" (Just "EUR")
declareMonoUnit "GBP" (Just "GBP")
declareMonoUnit "JPY" (Just "JPY")

type Currency unit = ( Show unit
                     , Unit unit
                     , DimOfUnit unit ~ unit
                     , DimFactorsOf unit ~ '[F unit One]
                     , CompatibleUnit DefaultLCSU unit )
data Money = forall u. Currency u => Money u (MkQu_U u)

getExchangeRate :: ( CompatibleUnit DefaultLCSU (to :/ from)
                   , Currency from, Currency to )
                => from -> to -> IO (Maybe (MkQu_U (to :/ from)))
getExchangeRate from to = runMaybeT $ do
  let request_string = "http://download.finance.yahoo.com/d/" ++
                       "quotes.csv?s=" ++ show from ++ show to ++
                       "=X&f=sl1d1t1ba&e=.csv"
  Right response <- lift $ simpleHTTP (getRequest request_string)
  ratio <- hoist_maybe $ parse_conversion_rate (rspBody response)
  return (ratio % (to :/ from))

  where
    parse_conversion_rate :: String -> Maybe Double
    parse_conversion_rate str = do
      (_ : rate_str : _) <- return $ splitOn "," str
      readMaybe rate_str
      
    hoist_maybe :: Monad m => Maybe a -> MaybeT m a
    hoist_maybe Nothing = mzero
    hoist_maybe (Just x) = return x

type Dollars = MkQu_U USD

sumInDollars :: [Money] -> IO Double
sumInDollars moneys = do
  converted <- mapM convert moneys
  return $ sum (map (# USD) converted)
  where
    convert :: Money -> IO Dollars
    convert (Money currency value) = do
      m_ratio <- getExchangeRate currency USD
      case m_ratio of
        Nothing -> fail "error"
        Just ratio -> return $ undefined -- ratio |*| value
