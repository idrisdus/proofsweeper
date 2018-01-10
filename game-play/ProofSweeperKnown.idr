-- Generated source - do not edit!
-- This contains the axioms for the current state of the game.
module ProofSweeperKnown

import ProofSweeperBase

%access public export
%default total

gridSize : Nat
gridSize = 5

mineNeighboursForSize : Coord -> List Coord
mineNeighboursForSize = mineNeighbours gridSize

data MineFact : Coord -> MineProp -> Type where
  KnownNotMineIsNotMine : MineFact c (KnownNotMine _) -> MineFact c IsNotMine
  AllMinesAccountedFor :
       (c : Coord)
    -> (cNonMine : Coord)
    -> (prfCIsNotMine : MineFact c (KnownNotMine cnt))
    -> (knownMines : List Coord)
    -> (prfEnoughKnownMines : distinctCount knownMines = cnt)
    -> (prfKnownMinesAreMines : (cNeigh : Coord)
           -> elem cNeigh knownMines = True
           -> MineFact cNeigh IsMine)
    -> (prfKnownMinesAreNeighbours : (cNeigh : Coord)
           -> elem cNeigh knownMines = True
           -> elem cNeigh (mineNeighboursForSize c) = True)
    -> (prfNonMineIsNeighbour : elem cNonMine (mineNeighboursForSize c) = True)
    -> (prfNonMineNotInKnownMines : elem cNonMine knownMines = False)
    -> MineFact cNonMine IsNotMine
  AllNonMinesAccountedFor :
       (c : Coord)
    -> (cMine : Coord)
    -> (prfCIsNotMine : MineFact c (KnownNotMine cnt))
    -> (knownNonMines : List Coord)
    -> (prfEnoughKnownNonMines : distinctCount knownNonMines + cnt = length (mineNeighboursForSize c))
    -> (prfKnownNonMinesAreNotMines : (cNeigh : Coord)
           -> elem cNeigh knownNonMines = True
           -> MineFact cNeigh IsNotMine)
    -> (prfKnownNonMinesAreNeighbours : (cNeigh : Coord)
           -> elem cNeigh knownNonMines = True
           -> elem cNeigh (mineNeighboursForSize c) = True)
    -> (prfNonMineIsNeighbour : elem cMine (mineNeighboursForSize c) = True)
    -> (prfMineNotInKnownNonMines : elem cMine knownNonMines = False)
    -> MineFact cMine IsMine
  NoMineAt2_0 : MineFact (MkCoord 2 0) (KnownNotMine 2)
  NoMineAt2_1 : MineFact (MkCoord 2 1) (KnownNotMine 2)
  NoMineAt2_2 : MineFact (MkCoord 2 2) (KnownNotMine 2)
  MineAt2_3 : MineFact (MkCoord 2 3) IsMine
  MineAt3_0 : MineFact (MkCoord 3 0) IsMine
  NoMineAt3_1 : MineFact (MkCoord 3 1) (KnownNotMine 2)
  NoMineAt3_2 : MineFact (MkCoord 3 2) (KnownNotMine 1)
  NoMineAt3_3 : MineFact (MkCoord 3 3) (KnownNotMine 2)
  MineAt4_0 : MineFact (MkCoord 4 0) IsMine
  NoMineAt4_1 : MineFact (MkCoord 4 1) (KnownNotMine 2)
  NoMineAt4_2 : MineFact (MkCoord 4 2) (KnownNotMine 0)
  NoMineAt4_3 : MineFact (MkCoord 4 3) (KnownNotMine 1)

-- TODO: See if we can prove this instead of asserting...
notNonMineImpliesMine : Not (MineFact c IsNotMine) -> MineFact c IsMine
notNonMineImpliesMine v = believe_me v
notMineImpliesNonMine : Not (MineFact c IsMine) -> MineFact c IsNotMine
notMineImpliesNonMine v = believe_me v
nonMineImpliesNotMine : MineFact c IsNotMine -> Not (MineFact c IsMine)
nonMineImpliesNotMine v = believe_me v
mineImpliesNotNonMine : MineFact c IsMine -> Not (MineFact c IsNotMine)
mineImpliesNotNonMine v = believe_me v
