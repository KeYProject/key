
/* 
   This example is referenced in the thesis on Java 5.

   The contract can be proven with 1267 nodes in 16 branches with
   one manual instantiation (expand dynamic types).
   
   Java does not recognize exhaustive matching in a switch statement
   so that the final throw statement is needed to avoid a missing- 
   return-statement error.
   
   KeY being aware of enum types can however prove that this
   exceptional case will never occur.

 */

enum Month { JAN, FEB, MAR, APR, MAY, JUN, JUL, AUG, SEP, OCT, NOV, DEC};


class Example {

    boolean leapYear;


    /*@ public normal_behavior 
      @   requires month != null;
      @   ensures \result > 0 && \result <= 31;
      @*/
    int daysInMoth(Month month) {
	switch(month) {
	case Month.JAN:
	case Month.MAR:
	case Month.MAY:
	case Month.JUL:
	case Month.AUG:
	case Month.OCT:
	case Month.DEC:
	    return 31;

	case Month.APR:
	case Month.JUN:
	case Month.SEP:
	case Month.NOV:
	    return 30;

	case Month.FEB:
	    return leapYear ? 29 : 28;
	}
	throw new Error();
    }

}
