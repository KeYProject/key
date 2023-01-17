package java.math;

public final class BigInteger extends java.lang.Number implements java.lang.Comparable {

   //@ public final ghost \bigint value;
    
   //@ public static invariant java.math.BigInteger.ZERO.value == (\bigint) 0;

   public static final java.math.BigInteger ZERO = BigInteger.valueOf(0);
   
   public static BigInteger valueOf(long v) {
       BigInteger result = new BigInteger();
       //@ set result.value = (\bigint) v;
       return result;
   }

   /*@ public normal_behavior
     @ requires true;
     @ ensures (\result <= 0) <==> (this.value - param0.value <= 0);
     @ ensures (\result >= 0) <==> (this.value - param0.value >= 0);
     @ assignable \strictly_nothing;
     @ determines \result \by this.value, param0.value;
     @*/
   public int compareTo(java.math.BigInteger param0);

   /*@ public normal_behavior
     @ requires true;
     @ ensures \result.value == this.value % param0.value;
     @ ensures \fresh(\result) && \fresh(\result.*) && \typeof(\result) == \type(BigInteger);
     @ assignable \nothing;
     @ determines \result \by \nothing \new_objects \result;
     @ determines \result.value \by this.value, param0.value;
     @*/
   public java.math.BigInteger mod(java.math.BigInteger param0);
}
