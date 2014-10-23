{- An example showing units of measure.
   Copyright (c) 2014 Richard Eisenberg
  -}

module Units where

import Data.Metrology
import Data.Metrology.SI
import Data.Units.US

import Data.Metrology.Show

journeyTime :: Length -> Velocity -> Time
journeyTime l v = l |/| v

nycToPhilly :: Length
nycToPhilly = 155.6 % kilo Meter

speedLimit :: Velocity
speedLimit = 55 % (Mile :/ Hour)

journeyHome :: Time
journeyHome = journeyTime nycToPhilly speedLimit
