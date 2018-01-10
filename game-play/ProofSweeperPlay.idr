module ProofSweeperPlay
import ProofSweeperKnown
import ProofSweeperBase
import ProofSweeperLemmas

%access public export

mineAt_4_0 : MineFact (MkCoord 4 0) IsMine
mineAt_4_0 =
  AllNonMinesAccountedFor
    (MkCoord 4 1)
    (MkCoord 4 0)
    NoMineAt4_1
    [(MkCoord 3 1),
     (MkCoord 3 2), (MkCoord 4 2)]
    Refl
    (trueForAllListElems3
      (\x => MineFact x IsNotMine) eqTestIsEqCoord
      (MkCoord 3 1)
      (MkCoord 3 2) (MkCoord 4 2)
      (KnownNotMineIsNotMine NoMineAt3_1)
      (KnownNotMineIsNotMine NoMineAt3_2)
      (KnownNotMineIsNotMine NoMineAt4_2)
    )
    (trueForAllListElems3
      (\x => elem x (mineNeighboursForSize (MkCoord 4 1)) = True) eqTestIsEqCoord
      (MkCoord 3 1) (MkCoord 3 2) (MkCoord 4 2)
      Refl Refl Refl
    )
    Refl
    Refl

mineAt_3_0 : MineFact (MkCoord 3 0) IsMine
mineAt_3_0 =
  AllNonMinesAccountedFor
    (MkCoord 4 1)
    (MkCoord 3 0)
    NoMineAt4_1
    [(MkCoord 3 1),
     (MkCoord 3 2), (MkCoord 4 2)]
    Refl
    (trueForAllListElems3
      (\x => MineFact x IsNotMine) eqTestIsEqCoord
      (MkCoord 3 1)
      (MkCoord 3 2) (MkCoord 4 2)
      (KnownNotMineIsNotMine NoMineAt3_1)
      (KnownNotMineIsNotMine NoMineAt3_2)
      (KnownNotMineIsNotMine NoMineAt4_2)
    )
    (trueForAllListElems3
      (\x => elem x (mineNeighboursForSize (MkCoord 4 1)) = True) eqTestIsEqCoord
      (MkCoord 3 1) (MkCoord 3 2) (MkCoord 4 2)
      Refl Refl Refl
    )
    Refl
    Refl

noMineAt_2_0 : MineFact (MkCoord 2 0) IsNotMine
noMineAt_2_0 =
  AllMinesAccountedFor
    (MkCoord 3 1)
    (MkCoord 2 0)
    NoMineAt3_1
    [(MkCoord 3 0), (MkCoord 4 0)]
    Refl
    (trueForAllListElems2
      (\x => MineFact x IsMine) eqTestIsEqCoord
      (MkCoord 3 0) (MkCoord 4 0)
      (MineAt3_0)
      (MineAt4_0)
    )
    (trueForAllListElems2
      (\x => elem x (mineNeighboursForSize (MkCoord 3 1)) = True) eqTestIsEqCoord
      (MkCoord 3 0) (MkCoord 4 0)
      Refl Refl
    )
    Refl
    Refl

noMineAt_2_1 : MineFact (MkCoord 2 1) IsNotMine
noMineAt_2_1 =
  AllMinesAccountedFor
    (MkCoord 3 1)
    (MkCoord 2 1)
    NoMineAt3_1
    [(MkCoord 3 0), (MkCoord 4 0)]
    Refl
    (trueForAllListElems2
      (\x => MineFact x IsMine) eqTestIsEqCoord
      (MkCoord 3 0) (MkCoord 4 0)
      (MineAt3_0)
      (MineAt4_0)
    )
    (trueForAllListElems2
      (\x => elem x (mineNeighboursForSize (MkCoord 3 1)) = True) eqTestIsEqCoord
      (MkCoord 3 0) (MkCoord 4 0)
      Refl Refl
    )
    Refl
    Refl

noMineAt_2_2 : MineFact (MkCoord 2 2) IsNotMine
noMineAt_2_2 =
  AllMinesAccountedFor
    (MkCoord 3 1)
    (MkCoord 2 2)
    NoMineAt3_1
    [(MkCoord 3 0), (MkCoord 4 0)]
    Refl
    (trueForAllListElems2
      (\x => MineFact x IsMine) eqTestIsEqCoord
      (MkCoord 3 0) (MkCoord 4 0)
      (MineAt3_0)
      (MineAt4_0)
    )
    (trueForAllListElems2
      (\x => elem x (mineNeighboursForSize (MkCoord 3 1)) = True) eqTestIsEqCoord
      (MkCoord 3 0) (MkCoord 4 0)
      Refl Refl
    )
    Refl
    Refl

mineAt_2_3 : MineFact (MkCoord 2 3) IsMine
mineAt_2_3 =
  AllNonMinesAccountedFor
    (MkCoord 3 2)
    (MkCoord 2 3)
    NoMineAt3_2
    [(MkCoord 2 1), (MkCoord 3 1), (MkCoord 4 1),
     (MkCoord 2 2),                (MkCoord 4 2),
                    (MkCoord 3 3), (MkCoord 4 3)]
    Refl
    (trueForAllListElems7
      (\x => MineFact x IsNotMine) eqTestIsEqCoord
      (MkCoord 2 1) (MkCoord 3 1) (MkCoord 4 1)
      (MkCoord 2 2)               (MkCoord 4 2)
                    (MkCoord 3 3) (MkCoord 4 3)
      (KnownNotMineIsNotMine NoMineAt2_1)
      (KnownNotMineIsNotMine NoMineAt3_1)
      (KnownNotMineIsNotMine NoMineAt4_1)
      (KnownNotMineIsNotMine NoMineAt2_2)
      (KnownNotMineIsNotMine NoMineAt4_2)
      (KnownNotMineIsNotMine NoMineAt3_3)
      (KnownNotMineIsNotMine NoMineAt4_3)
    )
    (trueForAllListElems7
      (\x => elem x (mineNeighboursForSize (MkCoord 3 2)) = True) eqTestIsEqCoord
      (MkCoord 2 1) (MkCoord 3 1) (MkCoord 4 1)
      (MkCoord 2 2)               (MkCoord 4 2)
                    (MkCoord 3 3) (MkCoord 4 3)
      Refl Refl Refl Refl Refl Refl Refl
    )
    Refl
    Refl