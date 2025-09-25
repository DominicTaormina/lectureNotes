// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not5(p: B, q: B, r: B): Unit = {
  Deduce(
    ( !(!p | !q) ) |- ( p & q )
      Proof(
        1 (  !(!p | !q) ) by Premise,

        //think of 2 separate proofs

        //first, prove p
        2 SubProof(
          3 Assume ( !p ),
          4 ( !p | !q ) by OrI1(3)
          5 ( F ) by NegE(4, 1)

          //goal: F
        ),
        6 ( p ) by pbC(2)
        //use pbC to conclude p
        //then, prove q

        //
    )
  )
}
