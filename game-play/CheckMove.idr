module CheckMove
  import ProofSweeperBase
  import ProofSweeperKnown
  import ProofSweeperPlay
  total
  checkMove : MineFact (MkCoord 2 3) IsMine
  checkMove = mineAt_2_3
