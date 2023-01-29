
public class BlockContractWithExceptionPostconditionNotVerified {
   /*@ exceptional_behavior
     @ requires x == 2;
     @ signals (NullPointerException e) true;
     @ assignable \nothing;
     @*/
   public static int main(int x) {
      return magic(x);
   }
   
   public static int magic(int x) {
      /*@ exceptional_behavior
        @ requires x == 2;
        @ signals_only NullPointerException;
        @ signals (NullPointerException e) true;
        @ assignable \nothing;
        @*/
      {
         if (x == 2) {
            throw new RuntimeException();
         }
      }
      return x;
   }
}
