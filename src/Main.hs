{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import           GHC.TypeLits
import           Data.Proxy
import           Data.Type.Bool
import           Data.Type.Equality
import qualified Data.List as L
import qualified Data.Char as C

type family (/=) (a :: Nat) (b :: Nat) where 
    (/=) a b = If (a == b) False True

type family (<) (a :: Nat) (b :: Nat) where 
    (<) a b = a <=? b && a /= b

type family (>) (a :: Nat) (b :: Nat) where 
    (>) a b = b <=? a && b /= a

type family (>=) (a :: Nat) (b :: Nat) where 
    (>=) a b = b <=? a

data Mem = Leaf | Node Nat Nat Mem Mem

type family Store (mem :: Mem) (addr :: Nat) (imm :: Nat) where
    Store Leaf addr imm = Node addr imm Leaf Leaf
    Store (Node a v left right) addr imm = If (a == addr) 
        (Node a imm left right)
        (Node a v (Store left addr imm) right)

--        (Node a v 
--            (If (a <=? addr) left (Store left addr imm))
--            (If (a <=? addr) (Store right addr imm) right))

type family Load (mem :: Mem) (addr :: Nat) where
    Load Leaf addr = 0x000000 -- 初期値は0に
    Load (Node a v left right) addr = If (a == addr) v (Load left addr)

--    Load (Node a v left right) addr = If (a == addr) v (
--        If (a <=? addr) (Load right addr) (Load left addr))

type family B24 (n :: Nat) where
    B24 n = Mod n 0x1000000

instance Show Mem where
    show (Leaf) = ""
    show (Node a v left right) = let
        in show left ++ "_:_" ++ " " ++ show right

data CPU (inputBuf :: [Nat]) (outputBuf :: [Nat]) (mem :: Mem) (pc :: Nat)
    (a :: Nat) (b :: Nat) (c :: Nat) (d :: Nat) (sp :: Nat) (bp :: Nat)

data Reg = PC | A | B | C | D | SP | BP

type family Get cpu (src :: Reg) where
    Get (CPU i o mem pc a b c d sp bp) src = 
        If (src == PC) pc 
        (If (src == A) a
        (If (src == B) b
        (If (src == C) c
        (If (src == D) d
        (If (src == SP) sp
        (If (src == BP) bp
        (0x0)))))))

type family GetMem cpu where
    GetMem (CPU _ _ mem _ _ _ _ _ _ _) = mem

type family GetInBuf cpu where
    GetInBuf (CPU i _ _ _ _ _ _ _ _ _) = i

type family GetOutBuf cpu where
    GetOutBuf (CPU _ o _ _ _ _ _ _ _ _) = o

type family ALITH_IMM (alith_id :: Nat) cpu (dst :: Reg) (imm :: Nat) where
    ALITH_IMM alith_id (CPU i o mem pc a b c d sp bp) dst imm = CPU i o mem (B24 (pc + 1))
        (If (A  == dst) (ALITH alith_id a  imm) a )
        (If (B  == dst) (ALITH alith_id b  imm) b )
        (If (C  == dst) (ALITH alith_id c  imm) c )
        (If (D  == dst) (ALITH alith_id d  imm) d )
        (If (SP == dst) (ALITH alith_id sp imm) sp)
        (If (BP == dst) (ALITH alith_id bp imm) bp)

type family ALITH (alith_id :: Nat) (l :: Nat) (r :: Nat) where
    ALITH 0 l r = B24 (l + r)
    ALITH 1 l r = B24 (l - r)
    ALITH 2 l r = If (l ==  r) 1 0
    ALITH 3 l r = If (l /=  r) 1 0
    ALITH 4 l r = If (l <   r) 1 0
    ALITH 5 l r = If (l >   r) 1 0
    ALITH 6 l r = If (l <=? r) 1 0
    ALITH 7 l r = If (l >=  r) 1 0

type family ADD where
    ADD = 0

type family SUB where
    SUB = 1

type family EQ where
    EQ = 2

type family NE where
    NE = 3

type family LT where
    LT = 4

type family GT where
    GT = 5

type family LE where
    LE = 6

type family GE where
    GE = 7

type family COND_JUMP_IMM_IMM (cond_id :: Nat) cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    COND_JUMP_IMM_IMM cond_id cpu jmp dst imm = CPU
        (GetInBuf cpu) (GetOutBuf cpu) (GetMem cpu)
        (If (COND cond_id (Get cpu dst) imm) (PC2ADDR (B24 jmp)) (B24 (Get cpu PC + 1)))
        (Get cpu A) (Get cpu B) (Get cpu C) (Get cpu D) (Get cpu SP) (Get cpu BP)

type family COND (cond_id :: Nat) l r where
    COND 0 l r = l == r
    COND 1 l r = l /= r
    COND 2 l r = l < r
    COND 3 l r = l > r
    COND 4 l r = l <=? r
    COND 5 l r = l >= r

type family COND_EQ where
    COND_EQ = 0

type family COND_NE where
    COND_NE = 1

type family COND_LT where
    COND_LT = 2

type family COND_GT where
    COND_GT = 3

type family COND_LE where
    COND_LE = 4

type family COND_GE where
    COND_GE = 5

-------- Inst --------

type family MV_IMM cpu (dst :: Reg) (imm :: Nat) where
    MV_IMM (CPU i o mem pc a b c d sp bp) dst imm = CPU 
        i o mem (B24 (pc + 1))
        (If (A  == dst) imm a )
        (If (B  == dst) imm b )
        (If (C  == dst) imm c )
        (If (D  == dst) imm d )
        (If (SP == dst) imm sp)
        (If (BP == dst) imm bp)

type family MV_REG cpu (dst :: Reg) (src :: Reg) where
    MV_REG cpu dst src = MV_IMM cpu dst (Get cpu src)

type family ADD_IMM cpu (dst :: Reg) (imm :: Nat) where
    ADD_IMM cpu dst imm = ALITH_IMM ADD cpu dst imm

type family ADD_REG cpu (dst :: Reg) (src :: Reg) where
    ADD_REG cpu dst src = ALITH_IMM ADD cpu dst (Get cpu src)

type family SUB_IMM cpu (dst :: Reg) (imm :: Nat) where
    SUB_IMM cpu dst imm = ALITH_IMM SUB cpu dst imm

type family SUB_REG cpu (dst :: Reg) (src :: Reg) where
    SUB_REG cpu dst src = ALITH_IMM SUB cpu dst (Get cpu src)
 
type family LOAD_IMM cpu (dst :: Reg) (imm :: Nat) where
    LOAD_IMM (CPU i o mem pc a b c d sp bp) dst imm = CPU 
        i o mem (B24 (pc + 1))
        (If (A  == dst) (Load mem imm) a )
        (If (B  == dst) (Load mem imm) b )
        (If (C  == dst) (Load mem imm) c )
        (If (D  == dst) (Load mem imm) d )
        (If (SP == dst) (Load mem imm) sp)
        (If (BP == dst) (Load mem imm) bp)

type family LOAD_REG cpu (dst :: Reg) (src :: Reg) where
    LOAD_REG cpu dst src = LOAD_IMM cpu dst (Get cpu src) 

type family STORE_IMM cpu (src :: Reg) (addr :: Nat) where
    STORE_IMM cpu src addr  = CPU
        (GetInBuf cpu) (GetOutBuf cpu)
        (Store (GetMem cpu) addr (Get cpu src))
        (B24 (Get cpu PC + 1))
        (Get cpu A) (Get cpu B) (Get cpu C) (Get cpu D) (Get cpu SP) (Get cpu BP)

type family STORE_REG cpu (src :: Reg) (addr :: Reg) where
    STORE_REG cpu src addr  = STORE_IMM cpu src (Get cpu addr)

type family JUMP_IMM cpu (jmp :: Nat) where
    JUMP_IMM (CPU i o mem pc a b c d sp bp) jmp = CPU i o mem (PC2ADDR (B24 jmp)) a b c d sp bp

type family JUMP_REG cpu (src :: Reg) where
    JUMP_REG cpu src = JUMP_IMM cpu (Get cpu src)

type family EQ_IMM cpu (dst :: Reg) (imm :: Nat) where
    EQ_IMM cpu dst imm = ALITH_IMM EQ cpu dst imm

type family EQ_REG cpu (dst :: Reg) (src :: Reg) where
    EQ_REG cpu dst src = ALITH_IMM EQ cpu dst (Get cpu src)

type family NE_IMM cpu (dst :: Reg) (imm :: Nat) where
    NE_IMM cpu dst imm = ALITH_IMM NE cpu dst imm

type family NE_REG cpu (dst :: Reg) (src :: Reg) where
    NE_REG cpu dst src = ALITH_IMM NE cpu dst (Get cpu src)


type family LT_IMM cpu (dst :: Reg) (imm :: Nat) where
    LT_IMM cpu dst imm = ALITH_IMM LT cpu dst imm

type family LT_REG cpu (dst :: Reg) (src :: Reg) where
    LT_REG cpu dst src = ALITH_IMM LT cpu dst (Get cpu src)

type family GT_IMM cpu (dst :: Reg) (imm :: Nat) where
    GT_IMM cpu dst imm = ALITH_IMM GT cpu dst imm

type family GT_REG cpu (dst :: Reg) (src :: Reg) where
    GT_REG cpu dst src = ALITH_IMM GT cpu dst (Get cpu src)

type family LE_IMM cpu (dst :: Reg) (imm :: Nat) where
    LE_IMM cpu dst imm = ALITH_IMM LE cpu dst imm

type family LE_REG cpu (dst :: Reg) (src :: Reg) where
    LE_REG cpu dst src = ALITH_IMM LE cpu dst (Get cpu src)

type family GE_IMM cpu (dst :: Reg) (imm :: Nat) where
    GE_IMM cpu dst imm = ALITH_IMM GE cpu dst imm

type family GE_REG cpu (dst :: Reg) (src :: Reg) where
    GE_REG cpu dst src = ALITH_IMM GE cpu dst (Get cpu src)

type family JEQ_IMM_IMM cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    JEQ_IMM_IMM cpu jmp dst imm = COND_JUMP_IMM_IMM COND_EQ cpu jmp dst imm

type family JEQ_IMM_REG cpu (jmp :: Nat) (dst :: Reg) (src :: Reg) where
    JEQ_IMM_REG cpu jmp dst src = JEQ_IMM_IMM cpu jmp dst (Get cpu src)

type family JEQ_REG_IMM cpu (jmp :: Reg) (dst :: Reg) (imm :: Nat) where
    JEQ_REG_IMM cpu jmp dst imm = JEQ_IMM_IMM cpu (Get cpu jmp) dst imm

type family JEQ_REG_REG cpu (jmp :: Reg) (dst :: Reg) (src :: Reg) where
    JEQ_REG_REG cpu jmp dst src = JEQ_IMM_IMM cpu (Get cpu jmp) dst (Get cpu src)

type family JNE_IMM_IMM cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    JNE_IMM_IMM cpu jmp dst imm = COND_JUMP_IMM_IMM COND_NE cpu jmp dst imm
    
type family JNE_IMM_REG cpu (jmp :: Nat) (dst :: Reg) (src :: Reg) where
    JNE_IMM_REG cpu jmp dst src = JNE_IMM_IMM cpu jmp dst (Get cpu src)

type family JNE_REG_IMM cpu (jmp :: Reg) (dst :: Reg) (imm :: Nat) where
    JNE_REG_IMM cpu jmp dst imm = JNE_IMM_IMM cpu (Get cpu jmp) dst imm

type family JNE_REG_REG cpu (jmp :: Reg) (dst :: Reg) (src :: Reg) where
    JNE_REG_REG cpu jmp dst src = JNE_IMM_IMM cpu (Get cpu jmp) dst (Get cpu src)

type family JLT_IMM_IMM cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    JLT_IMM_IMM cpu jmp dst imm = COND_JUMP_IMM_IMM COND_LT cpu jmp dst imm

type family JLT_IMM_REG cpu (jmp :: Nat) (dst :: Reg) (src :: Reg) where
    JLT_IMM_REG cpu jmp dst src = JLT_IMM_IMM cpu jmp dst (Get cpu src)

type family JLT_REG_IMM cpu (jmp :: Reg) (dst :: Reg) (imm :: Nat) where
    JLT_REG_IMM cpu jmp dst imm = JLT_IMM_IMM cpu (Get cpu jmp) dst imm

type family JLT_REG_REG cpu (jmp :: Reg) (dst :: Reg) (src :: Reg) where
    JLT_REG_REG cpu jmp dst src = JLT_IMM_IMM cpu (Get cpu jmp) dst (Get cpu src)

type family JGT_IMM_IMM cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    JGT_IMM_IMM cpu jmp dst imm = COND_JUMP_IMM_IMM COND_GT cpu jmp dst imm

type family JGT_IMM_REG cpu (jmp :: Nat) (dst :: Reg) (src :: Reg) where
    JGT_IMM_REG cpu jmp dst src = JGT_IMM_IMM cpu jmp dst (Get cpu src)

type family JGT_REG_IMM cpu (jmp :: Reg) (dst :: Reg) (imm :: Nat) where
    JGT_REG_IMM cpu jmp dst imm = JGT_IMM_IMM cpu (Get cpu jmp) dst imm

type family JGT_REG_REG cpu (jmp :: Reg) (dst :: Reg) (src :: Reg) where
    JGT_REG_REG cpu jmp dst src = JGT_IMM_IMM cpu (Get cpu jmp) dst (Get cpu src)

type family JLE_IMM_IMM cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    JLE_IMM_IMM cpu jmp dst imm = COND_JUMP_IMM_IMM COND_LE cpu jmp dst imm

type family JLE_IMM_REG cpu (jmp :: Nat) (dst :: Reg) (src :: Reg) where
    JLE_IMM_REG cpu jmp dst src = JLE_IMM_IMM cpu jmp dst (Get cpu src)

type family JLE_REG_IMM cpu (jmp :: Reg) (dst :: Reg) (imm :: Nat) where
    JLE_REG_IMM cpu jmp dst imm = JLE_IMM_IMM cpu (Get cpu jmp) dst imm

type family JLE_REG_REG cpu (jmp :: Reg) (dst :: Reg) (src :: Reg) where
    JLE_REG_REG cpu jmp dst src = JLE_IMM_IMM cpu (Get cpu jmp) dst (Get cpu src)

type family JGE_IMM_IMM cpu (jmp :: Nat) (dst :: Reg) (imm :: Nat) where
    JGE_IMM_IMM cpu jmp dst imm = COND_JUMP_IMM_IMM COND_GE cpu jmp dst imm

type family JGE_IMM_REG cpu (jmp :: Nat) (dst :: Reg) (src :: Reg) where
    JGE_IMM_REG cpu jmp dst src = JGE_IMM_IMM cpu jmp dst (Get cpu src)

type family JGE_REG_IMM cpu (jmp :: Reg) (dst :: Reg) (imm :: Nat) where
    JGE_REG_IMM cpu jmp dst imm = JGE_IMM_IMM cpu (Get cpu jmp) dst imm

type family JGE_REG_REG cpu (jmp :: Reg) (dst :: Reg) (src :: Reg) where
    JGE_REG_REG cpu jmp dst src = JGE_IMM_IMM cpu (Get cpu jmp) dst (Get cpu src)

type family PUTC_IMM cpu (imm :: Nat) where
    PUTC_IMM (CPU i o mem pc a b c d sp bp) imm = CPU
        i (imm : o) mem (B24 (pc + 1)) a b c d sp bp

type family PUTC_REG cpu (src :: Reg) where
    PUTC_REG cpu src = PUTC_IMM cpu (Get cpu src)

type family GETC cpu (dst :: Reg) where
    GETC (CPU '[] o mem pc a b c d sp bp) dst = CPU 
        '[] o mem (B24 (pc + 1))
        (If (A  == dst) 0 a )
        (If (B  == dst) 0 b )
        (If (C  == dst) 0 c )
        (If (D  == dst) 0 d )
        (If (SP == dst) 0 sp)
        (If (BP == dst) 0 bp)
    GETC (CPU (i : is) o mem pc a b c d sp bp) dst = CPU
        is o mem (B24 (pc + 1))
        (If (A  == dst) i a )
        (If (B  == dst) i b )
        (If (C  == dst) i c )
        (If (D  == dst) i d )
        (If (SP == dst) i sp)
        (If (BP == dst) i bp)

type family NOP cpu where
    NOP (CPU i o mem pc a b c d sp bp) = CPU i o mem (B24 (pc + 1)) a b c d sp bp

class KnownNats a where
    natVals :: proxy a -> [Integer]

instance KnownNats '[] where
    natVals _ = []

instance (KnownNat x, KnownNats xs) => KnownNats (x ': xs) where
    natVals _ = natVal (Proxy :: Proxy x) : natVals (Proxy :: Proxy xs)

instance KnownNats Leaf where
    natVals _ = []

instance (KnownNat addr, KnownNat v, KnownNats l, KnownNats r) => KnownNats (Node addr v l r) where
    natVals _ = natVals (Proxy :: Proxy l)
             ++ [natVal (Proxy :: Proxy addr), natVal (Proxy :: Proxy v)] 
             ++ natVals (Proxy :: Proxy r)

showState :: forall i o mem pc a b c d sp bp
           . (KnownNats i, KnownNats o, KnownNats mem, KnownNat pc, KnownNat a, KnownNat b, KnownNat c, KnownNat d, KnownNat sp, KnownNat bp)
          => Proxy (CPU i o mem pc a b c d sp bp) -> String
showState Proxy = let
        o_num = show . reverse $ natVals (Proxy :: Proxy o)
        o_str = map (C.chr . fromInteger) . L.reverse $ natVals (Proxy :: Proxy o)
        mem   = show $ natVals (Proxy :: Proxy mem)
        pc    = show $ natVal (Proxy :: Proxy pc)
        a     = show $ natVal (Proxy :: Proxy a)
        b     = show $ natVal (Proxy :: Proxy b)
        c     = show $ natVal (Proxy :: Proxy c)
        d     = show $ natVal (Proxy :: Proxy d)
        sp    = show $ natVal (Proxy :: Proxy sp)
        bp    = show $ natVal (Proxy :: Proxy bp)
        in concat ["output(num):\n", o_num, "\noutput(str):\n", o_str,
            "\nMEM: ", mem,
            "\nPC: ", pc, ", A: ", a, ", B: ", b, ", C: ", c, ", d: ", d, ", SP: ", sp, ", BP: ", bp]

showDebug :: forall buf. (KnownNats buf) => Proxy buf -> [Integer]
showDebug Proxy = reverse $ natVals (Proxy :: Proxy buf)

showOutput :: forall i o mem pc a b c d sp bp
            . (KnownNats o) 
           => Proxy (CPU i o mem pc a b c d sp bp) -> String
showOutput Proxy = map (C.chr . fromInteger) . L.reverse $ natVals (Proxy :: Proxy o)


type Mem0 = Init 0 Leaf
type CPU0 = CPU '[] '[] Mem0 0 0 0 0 0 0 0

type family Run_ (total_cnt :: Nat) (debug :: [Nat]) cpu where
    Run_ total_cnt debug cpu = Run total_cnt debug (Get cpu PC) cpu

main :: IO ()
main = do
    -- putStrLn $ showState (Proxy :: Proxy (Run 0 '[] 0 CPU0))
    putStrLn $ showOutput (Proxy :: Proxy (Run 0 '[] 0 CPU0))

------------

type family Init (pc :: Nat) (mem :: Mem) where
 Init      0 mem = Init 1 (Store mem 0 1)
 Init _ mem = mem

type family PC2ADDR (pc :: Nat) where
 PC2ADDR      0 = 0
 PC2ADDR      1 = 1
 PC2ADDR      2 = 43
 PC2ADDR      3 = 114
 PC2ADDR      4 = 130
 PC2ADDR      5 = 132
 PC2ADDR      6 = 133
 PC2ADDR      7 = 237
 PC2ADDR      8 = 251
 PC2ADDR      9 = 257
 PC2ADDR     10 = 301
 PC2ADDR     11 = 356
 PC2ADDR     12 = 369
 PC2ADDR     13 = 370
 PC2ADDR     14 = 384
 PC2ADDR     15 = 426
 PC2ADDR     16 = 458
 PC2ADDR     17 = 471
 PC2ADDR     18 = 478
 PC2ADDR     19 = 488
 PC2ADDR     20 = 501
 PC2ADDR     21 = 502
 PC2ADDR     22 = 503
 PC2ADDR     23 = 534
 PC2ADDR     24 = 546
 PC2ADDR     25 = 578
 PC2ADDR     26 = 603
 PC2ADDR     27 = 615
 PC2ADDR     28 = 647
 PC2ADDR     29 = 652
 PC2ADDR     30 = 670
 PC2ADDR     31 = 677
 PC2ADDR     32 = 691

type family Run (total_cnt :: Nat) (debug :: [Nat]) (pc :: Nat) cpu where
 Run 5000 debug _ cpu = cpu
 Run total_cnt debug      0 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 18)
 Run total_cnt debug      1 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug      2 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug      3 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu BP D)
 Run total_cnt debug      4 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug      5 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu BP SP)
 Run total_cnt debug      6 cpu = Run_ (total_cnt + 1) debug (SUB_IMM cpu SP 52)
 Run total_cnt debug      7 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 1)
 Run total_cnt debug      8 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug      9 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     10 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug     11 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     12 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug     13 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777168)
 Run total_cnt debug     14 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug     15 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     16 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug     17 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     18 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug     19 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     20 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug     21 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     22 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug     23 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     24 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     25 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     26 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug     27 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug     28 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     29 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     30 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     31 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug     32 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug     33 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     34 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     35 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug     36 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B A)
 Run total_cnt debug     37 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     38 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     39 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug     40 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     41 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug     42 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug     43 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     44 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 3)
 Run total_cnt debug     45 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug     46 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug     47 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     48 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug     49 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     50 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug     51 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777192)
 Run total_cnt debug     52 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug     53 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     54 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug     55 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     56 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug     57 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     58 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug     59 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     60 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     61 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug     62 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug     63 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     64 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     65 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     66 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug     67 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug     68 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     69 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     70 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     71 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug     72 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug     73 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     74 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     75 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug     76 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B A)
 Run total_cnt debug     77 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     78 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     79 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug     80 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B SP)
 Run total_cnt debug     81 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     82 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 3)
 Run total_cnt debug     83 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug     84 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug     85 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug     86 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug     87 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug     88 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     89 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 3)
 Run total_cnt debug     90 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug     91 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug     92 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug     93 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug     94 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug     95 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     96 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777166)
 Run total_cnt debug     97 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug     98 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug     99 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 2)
 Run total_cnt debug    100 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    101 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    102 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    103 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    104 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    105 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    106 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777166)
 Run total_cnt debug    107 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    108 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    109 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    110 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    111 cpu = Run_ (total_cnt + 1) debug (LT_REG cpu A B)
 Run total_cnt debug    112 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu B 1)
 Run total_cnt debug    113 cpu = Run_ (total_cnt + 1) debug (JNE_IMM_IMM cpu 4 A 0)
 Run total_cnt debug    114 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    115 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777166)
 Run total_cnt debug    116 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    117 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    118 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    119 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    120 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    121 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    122 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 3)
 Run total_cnt debug    123 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    124 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    125 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    126 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    127 cpu = Run_ (total_cnt + 1) debug (LT_REG cpu A B)
 Run total_cnt debug    128 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    129 cpu = Run_ (total_cnt + 1) debug (NE_IMM cpu B 0)
 Run total_cnt debug    130 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A B)
 Run total_cnt debug    131 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 6 A 0)
 Run total_cnt debug    132 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 8)
 Run total_cnt debug    133 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug    134 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777168)
 Run total_cnt debug    135 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    136 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    137 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    138 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    139 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    140 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    141 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    142 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    143 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    144 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    145 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    146 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    147 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    148 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    149 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    150 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    151 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    152 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    153 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    154 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    155 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    156 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    157 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    158 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    159 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    160 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    161 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug    162 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777168)
 Run total_cnt debug    163 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    164 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    165 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    166 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    167 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    168 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    169 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    170 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    171 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    172 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    173 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    174 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    175 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    176 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    177 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    178 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    179 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    180 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    181 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    182 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    183 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    184 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    185 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    186 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    187 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    188 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    189 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    190 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    191 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    192 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    193 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug    194 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777168)
 Run total_cnt debug    195 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    196 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    197 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    198 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    199 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    200 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    201 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    202 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    203 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    204 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    205 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    206 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    207 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    208 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    209 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    210 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 1)
 Run total_cnt debug    211 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    212 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    213 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    214 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    215 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    216 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    217 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    218 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    219 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    220 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    221 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    222 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    223 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    224 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    225 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    226 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    227 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    228 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B A)
 Run total_cnt debug    229 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    230 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    231 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    232 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777166)
 Run total_cnt debug    233 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    234 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    235 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 3)
 Run total_cnt debug    236 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    237 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    238 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    239 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    240 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    241 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    242 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    243 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    244 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 1)
 Run total_cnt debug    245 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    246 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    247 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    248 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    249 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    250 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 2)
 Run total_cnt debug    251 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    252 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B SP)
 Run total_cnt debug    253 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    254 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777165)
 Run total_cnt debug    255 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    256 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    257 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    258 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B SP)
 Run total_cnt debug    259 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug    260 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777192)
 Run total_cnt debug    261 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    262 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    263 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    264 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    265 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    266 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    267 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    268 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    269 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    270 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    271 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    272 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    273 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    274 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    275 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    276 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    277 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    278 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    279 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    280 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    281 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    282 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    283 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    284 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777164)
 Run total_cnt debug    285 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    286 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    287 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777164)
 Run total_cnt debug    288 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    289 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    290 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    291 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    292 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    293 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    294 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 2)
 Run total_cnt debug    295 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    296 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    297 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    298 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    299 cpu = Run_ (total_cnt + 1) debug (LE_REG cpu A B)
 Run total_cnt debug    300 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 11 A 0)
 Run total_cnt debug    301 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    302 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777165)
 Run total_cnt debug    303 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    304 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    305 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    306 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    307 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    308 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug    309 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777168)
 Run total_cnt debug    310 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    311 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    312 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    313 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    314 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    315 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    316 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    317 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    318 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    319 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    320 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    321 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    322 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    323 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    324 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    325 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    326 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    327 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    328 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    329 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    330 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    331 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    332 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    333 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    334 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    335 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    336 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    337 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777165)
 Run total_cnt debug    338 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    339 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    340 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 2)
 Run total_cnt debug    341 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    342 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    343 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    344 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    345 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    346 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    347 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777164)
 Run total_cnt debug    348 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    349 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    350 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    351 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    352 cpu = Run_ (total_cnt + 1) debug (SUB_REG cpu A B)
 Run total_cnt debug    353 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    354 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 2)
 Run total_cnt debug    355 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    356 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    357 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    358 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    359 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    360 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    361 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    362 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    363 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    364 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    365 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    366 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    367 cpu = Run_ (total_cnt + 1) debug (EQ_REG cpu A B)
 Run total_cnt debug    368 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 13 A 0)
 Run total_cnt debug    369 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 14)
 Run total_cnt debug    370 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    371 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    372 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    373 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    374 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    375 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    376 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    377 cpu = Run_ (total_cnt + 1) debug (SUB_IMM cpu A 1)
 Run total_cnt debug    378 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    379 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777167)
 Run total_cnt debug    380 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    381 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    382 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    383 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 9)
 Run total_cnt debug    384 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    385 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777165)
 Run total_cnt debug    386 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    387 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    388 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    389 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    390 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    391 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    392 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 4)
 Run total_cnt debug    393 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    394 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    395 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    396 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    397 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    398 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B A)
 Run total_cnt debug    399 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    400 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    401 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    402 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 2)
 Run total_cnt debug    403 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    404 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    405 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    406 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    407 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    408 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    409 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 4)
 Run total_cnt debug    410 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    411 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu C A)
 Run total_cnt debug    412 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    413 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    414 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A C)
 Run total_cnt debug    415 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 1)
 Run total_cnt debug    416 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B A)
 Run total_cnt debug    417 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    418 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    419 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP BP)
 Run total_cnt debug    420 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    421 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    422 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu BP A)
 Run total_cnt debug    423 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    424 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    425 cpu = Run_ (total_cnt + 1) debug (JUMP_REG cpu A)
 Run total_cnt debug    426 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    427 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    428 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu BP D)
 Run total_cnt debug    429 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    430 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu BP SP)
 Run total_cnt debug    431 cpu = Run_ (total_cnt + 1) debug (SUB_IMM cpu SP 2)
 Run total_cnt debug    432 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A BP)
 Run total_cnt debug    433 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 16777214)
 Run total_cnt debug    434 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    435 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    436 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    437 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    438 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    439 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 3)
 Run total_cnt debug    440 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    441 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    442 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    443 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    444 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    445 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    446 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 2)
 Run total_cnt debug    447 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    448 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    449 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    450 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    451 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    452 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 16)
 Run total_cnt debug    453 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    454 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    455 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    456 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    457 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 1)
 Run total_cnt debug    458 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A B)
 Run total_cnt debug    459 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 3)
 Run total_cnt debug    460 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    461 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    462 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    463 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    464 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP BP)
 Run total_cnt debug    465 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    466 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    467 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu BP A)
 Run total_cnt debug    468 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    469 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    470 cpu = Run_ (total_cnt + 1) debug (JUMP_REG cpu A)
 Run total_cnt debug    471 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP BP)
 Run total_cnt debug    472 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    473 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    474 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu BP A)
 Run total_cnt debug    475 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    476 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    477 cpu = Run_ (total_cnt + 1) debug (JUMP_REG cpu A)
 Run total_cnt debug    478 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    479 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    480 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu BP D)
 Run total_cnt debug    481 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    482 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu BP SP)
 Run total_cnt debug    483 cpu = Run_ (total_cnt + 1) debug (SUB_IMM cpu SP 2)
 Run total_cnt debug    484 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 1)
 Run total_cnt debug    485 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    486 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    487 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    488 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    489 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    490 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    491 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    492 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    493 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    494 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    495 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 10)
 Run total_cnt debug    496 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    497 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    498 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    499 cpu = Run_ (total_cnt + 1) debug (LE_REG cpu A B)
 Run total_cnt debug    500 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 21 A 0)
 Run total_cnt debug    501 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 22)
 Run total_cnt debug    502 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 32)
 Run total_cnt debug    503 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    504 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B SP)
 Run total_cnt debug    505 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    506 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777214)
 Run total_cnt debug    507 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    508 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    509 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    510 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    511 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    512 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    513 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    514 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    515 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    516 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 3)
 Run total_cnt debug    517 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    518 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    519 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    520 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    521 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    522 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    523 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    524 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    525 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    526 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    527 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    528 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 23)
 Run total_cnt debug    529 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    530 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    531 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    532 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    533 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 15)
 Run total_cnt debug    534 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A B)
 Run total_cnt debug    535 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 2)
 Run total_cnt debug    536 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    537 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    538 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    539 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    540 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    541 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    542 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    543 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    544 cpu = Run_ (total_cnt + 1) debug (EQ_REG cpu A B)
 Run total_cnt debug    545 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 25 A 0)
 Run total_cnt debug    546 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 70)
 Run total_cnt debug    547 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    548 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    549 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    550 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    551 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    552 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    553 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 105)
 Run total_cnt debug    554 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    555 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    556 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    557 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    558 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    559 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    560 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 122)
 Run total_cnt debug    561 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    562 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    563 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    564 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    565 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    566 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    567 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 122)
 Run total_cnt debug    568 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    569 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    570 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    571 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    572 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    573 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    574 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 1)
 Run total_cnt debug    575 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    576 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777214)
 Run total_cnt debug    577 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    578 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    579 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    580 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    581 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    582 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    583 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    584 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    585 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 5)
 Run total_cnt debug    586 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    587 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    588 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    589 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    590 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    591 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu B D)
 Run total_cnt debug    592 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    593 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    594 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    595 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    596 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    597 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 26)
 Run total_cnt debug    598 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    599 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    600 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    601 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    602 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 15)
 Run total_cnt debug    603 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu A B)
 Run total_cnt debug    604 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 2)
 Run total_cnt debug    605 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    606 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    607 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    608 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    609 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    610 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    611 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    612 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    613 cpu = Run_ (total_cnt + 1) debug (EQ_REG cpu A B)
 Run total_cnt debug    614 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 28 A 0)
 Run total_cnt debug    615 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 66)
 Run total_cnt debug    616 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    617 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    618 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    619 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    620 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    621 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    622 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 117)
 Run total_cnt debug    623 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    624 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    625 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    626 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    627 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    628 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    629 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 122)
 Run total_cnt debug    630 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    631 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    632 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    633 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    634 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    635 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    636 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 122)
 Run total_cnt debug    637 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    638 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    639 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    640 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    641 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    642 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    643 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 1)
 Run total_cnt debug    644 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    645 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777214)
 Run total_cnt debug    646 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    647 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    648 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777214)
 Run total_cnt debug    649 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    650 cpu = Run_ (total_cnt + 1) debug (EQ_IMM cpu A 0)
 Run total_cnt debug    651 cpu = Run_ (total_cnt + 1) debug (JEQ_IMM_IMM cpu 30 A 0)
 Run total_cnt debug    652 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 48)
 Run total_cnt debug    653 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    654 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    655 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    656 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    657 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    658 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    659 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    660 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    661 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    662 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    663 cpu = Run_ (total_cnt + 1) debug (ADD_REG cpu A B)
 Run total_cnt debug    664 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    665 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    666 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    667 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    668 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    669 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    670 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 10)
 Run total_cnt debug    671 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    672 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    673 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    674 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    675 cpu = Run_ (total_cnt + 1) debug (PUTC_REG cpu A)
 Run total_cnt debug    676 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    677 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    678 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    679 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A B)
 Run total_cnt debug    680 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu D SP)
 Run total_cnt debug    681 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu D 16777215)
 Run total_cnt debug    682 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A D)
 Run total_cnt debug    683 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu SP D)
 Run total_cnt debug    684 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu A 1)
 Run total_cnt debug    685 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B BP)
 Run total_cnt debug    686 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu B 16777215)
 Run total_cnt debug    687 cpu = Run_ (total_cnt + 1) debug (STORE_REG cpu A B)
 Run total_cnt debug    688 cpu = Run_ (total_cnt + 1) debug (LOAD_REG cpu A SP)
 Run total_cnt debug    689 cpu = Run_ (total_cnt + 1) debug (ADD_IMM cpu SP 1)
 Run total_cnt debug    690 cpu = Run_ (total_cnt + 1) debug (JUMP_IMM cpu 19)
 Run total_cnt debug    691 cpu = Run_ (total_cnt + 1) debug (MV_IMM cpu A 0)
 Run total_cnt debug    692 cpu = Run_ (total_cnt + 1) debug (MV_REG cpu B A)
 Run total_cnt debug    693 cpu = cpu
 Run total_cnt debug    694 cpu = cpu
