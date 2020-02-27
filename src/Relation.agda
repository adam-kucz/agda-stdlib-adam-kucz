{-# OPTIONS --exact-split --safe --prop #-}
module Relation where

import Relation.Binary
import Relation.Unary

module Bin = Relation.Binary
open Bin public hiding (Rel; RelProperty)
module Un = Relation.Unary
open Un public hiding (Rel; RelProperty)
