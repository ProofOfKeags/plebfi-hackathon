{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
module MiniScript where

import           Data.Bool                      ( (&&) )
import           Data.Kind                      ( Type )
import           Data.Singletons.Prelude.Bool
import           Data.Word                      ( Word32 )
import           GHC.TypeLits                   ( Nat )
import           GHC.TypeNats                   ( type (+) )
import           Haskoin.Crypto.Hash

data Key = Key
instance Show Key where
    show Key = "<key>"

data FragmentType
    = B
    | V
    | K
    | W

type T = True
type F = False

class BKV (a :: FragmentType)
instance BKV B
instance BKV K
instance BKV V
instance BKV W

type MiniScriptOp :: FragmentType -> Bool -> Bool -> Bool -> Bool -> Bool -> Type
data MiniScriptOp t z o n d u where
    Zero ::MiniScriptOp B T F F T T
    One ::MiniScriptOp B T F F F T
    Pk_k ::Key -> MiniScriptOp K F T T T T -- this is wrong: pushing a key consumes nothing from stack
    Pk_h ::Key -> MiniScriptOp K F F T T T -- this is wrong: the script clears all stack elements that are pushed
    Older ::Word32 -> MiniScriptOp B T F F F F
    After ::Word32 -> MiniScriptOp B T F F F F
    Sha256 ::Hash256 -> MiniScriptOp B F T T T T
    Ripemd160::Hash160 -> MiniScriptOp B F T T T T
    Hash256::Hash256 -> MiniScriptOp B F T T T T
    Hash160::Hash160 -> MiniScriptOp B F T T T T
    AndOr::BKV t =>
        MiniScriptOp B zx ox nx T T ->
        MiniScriptOp t zy oy ny dy uy ->
        MiniScriptOp t zz oz nz dz uz ->
        MiniScriptOp t (zx && zy && zz) (zx && oy && oz || ox && zy && zz) F dz (uy && uz)
    And_v::BKV ty =>
        MiniScriptOp V zx ox nx dx ux ->
        MiniScriptOp ty zy oy ny dy uy ->
        MiniScriptOp ty (zx && zy) (zx && oy || zy && ox) (nx || zx && ny) F uy
    And_b::MiniScriptOp B zx ox nx dx ux ->
        MiniScriptOp W zy oy ny dy uy ->
        MiniScriptOp B (zx && zy) (zx && oy || zy && ox) (nx || zx && ny) (dx && dy) T
    Or_b::MiniScriptOp B zx ox nx T ux ->
        MiniScriptOp W zz oz nz T uz ->
        MiniScriptOp B (zx && zz) (zx && oz || zz && ox) (nx || zx && nz) T T
    Or_c::MiniScriptOp B zx ox nx T T -> MiniScriptOp V zz oz nz dz uz -> MiniScriptOp V (zx && zz) (ox && zz) F F F
    Or_d::MiniScriptOp B zx ox nx T T -> MiniScriptOp B zz oz nz dz uz -> MiniScriptOp B (zx && zz) (ox && zz) F dz uz
    Or_i::BKV t =>
        MiniScriptOp t zx ox nx dx ux ->
        MiniScriptOp t zz oz nz dz uz ->
        MiniScriptOp t F (zx && zz) F (dx || dz) (ux && uz)
    Thresh::Thresh z o -> MiniScriptOp B z o F T T
    Multi::Multi -> MiniScriptOp B F F T T T
    Ax::MiniScriptOp B z o n d u -> MiniScriptOp W F F F T T
    Sx::MiniScriptOp B z T n d u -> MiniScriptOp W F F F T T
    Cx::MiniScriptOp K z o n d u -> MiniScriptOp B F o n d T -- this is wrong: o is not preserved since checksig consumes at least 2 elements from the stack
    Dx::MiniScriptOp V T o n d u -> MiniScriptOp B F T T T T
    Vx::MiniScriptOp B z o n d u -> MiniScriptOp V z o n F F
    Jx::MiniScriptOp B z o T d u -> MiniScriptOp B F o T T u
    Nx::MiniScriptOp B z o n d u -> MiniScriptOp B z o n d T


type ThreshWater :: Bool -> Bool -> Type
data ThreshWater z o where
    ThreshWaterBase ::MiniScriptOp B zx1 ox1 nx1 T T ->
        MiniScriptOp W zx2 ox2 nx2 T T ->
        MiniScriptOp W zx3 ox3 nx3 T T ->
        ThreshWater (zx1 && zx2 && zx3) (zx1 && zx2 && ox3 || zx1 && ox2 && zx3 || ox1 && zx2 && zx3)
    ThreshWaterCons ::ThreshWater z o -> MiniScriptOp W zx ox nx T T -> ThreshWater (z && zx) (o && Not ox || z && ox)

type Thresh :: Bool -> Bool -> Type
data Thresh z o where
    ThreshBase ::ThreshWater z o -> Thresh z o
    ThreshCons ::Thresh z o -> MiniScriptOp W zx ox nx dx ux -> Thresh (z && zx) (o && Not ox || z && ox)

data MultiWater where
    MultiWaterBase ::Key -> MultiWater
    MultiWaterCons ::MultiWater -> Key -> MultiWater

data Multi where
    MultiBase ::MultiWater -> Multi
    MultiCons ::Multi -> Key -> Multi
