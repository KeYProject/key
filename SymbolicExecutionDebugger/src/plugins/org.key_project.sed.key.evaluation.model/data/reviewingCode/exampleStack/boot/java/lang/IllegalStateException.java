package java.lang;

public class IllegalStateException extends java.lang.RuntimeException {
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public IllegalStateException(java.lang.String param0) {
      super(param0);
   }
}