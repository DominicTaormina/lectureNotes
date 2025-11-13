// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?
Contract(
  Requires(y >= 0),
  Ensures(Res[Z]  == x * y)
)

  var total: Z = 0
  var i: Z = 0

  //what goes here?

  //prove the invariant(s) is true before the loop begins
  Deduce(
    1 ( total == 0 ) bt Premise,  //from assignment
    2 ( i == 0 ) by Premise, //from assignment
    3 (  )
    
    //want: total == x*i
  )

  while (i != y) {
    //what goes here?
    Invariant(
      Modifies(i, total),
      total == x*i
    )

    //don't need this block (won't lose information)
    Deduce(
      1 ( total == x*i ) by Premise, //from invariant
    )

    //assume the invariant(s) are true here

    total = total + x

    Deduce(
      1 ( Old(total) == x*i ) by Premise, //from invariant, total has change
      2 ( total == Old(total) + x ) by Premise, //from assignment
      3 ( total == x * i + x ) by Algebra*(1, 2) //get rid of Old to summarize
    )
  
    i = i + 1

    Deduce(
      1 ( i == Old(i) + 1 ) by Premise, //from previous assignment
      2 ( total == x*Old(i) + x ) by Premise, //from previous blok, i has
      3 ( total == x*(i-1) + x ) by Algebra*(1, 2),
      4 ( total == x*i - x + x ) by Algebra*(3),
      5 ( total == x*i ) by Algebra*(4)
    )

    //proves invariant(s) still true at the end of an iteration

    //what should we be able to assert here?
  }

  //what do we need here?

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

var ans: Z = mult(a, b)

//what do we want to assert that ans is?
