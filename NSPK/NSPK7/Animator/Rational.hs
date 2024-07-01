module Rational(fract, numerator, denominator) where

  import qualified Data.Ratio
  import Data.Ratio(numerator, denominator)

  fract (a, b) = a Data.Ratio.% b
