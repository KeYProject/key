
public class LightweightOperationContractTest {
   public static int main(int x) {
      return magic(x);
   }
   
   /*@ requires x > 0;
     @ ensures \result == 1;
     @ also
     @ requires x < 0;
     @ ensures \result == -1;
     @ also
     @ requires x == 0;
     @ signals (NullPointerException) true;
     @*/
   public static int magic(int x) {
      return x;
   }
}
