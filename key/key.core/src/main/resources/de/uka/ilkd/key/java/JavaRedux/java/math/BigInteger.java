package java.math;

public class BigInteger extends java.lang.Number implements java.lang.Comparable {

   public final int value;

   //@ public static invariant ZERO.value == 0;
   public static final java.math.BigInteger ZERO;

   /*@ public behavior
     @ requires true;
     @ ensures (\result <= 0) <==> (this.value - param0.value <= 0);
     @ ensures (\result >= 0) <==> (this.value - param0.value >= 0);
     @ assignable \strictly_nothing;
     @ determines \result \by this.value, param0.value;
     @*/
   public int compareTo(java.math.BigInteger param0);

   /*@ public behavior
     @ requires true;
     @ ensures \result.value == this.value % param0.value;
     @ assignable \nothing;
     @ determines \result.value \by this.value, param0.value;
     @*/
   public java.math.BigInteger mod(java.math.BigInteger param0);
}