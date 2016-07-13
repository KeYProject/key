
public class BlockContractPreconditionNotVerified {
   /*@ normal_behavior
     @ requires x == 2;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main(int x) {
      return magic(x);
   }
   
   public static int magic(int x) {
      /*@ return_behavior
        @ requires x == 4711;
        @ returns \result == -2;
        @ assignable \strictly_nothing;
        @*/
      {
         if (x == 2) {
            return -4711;
         }
      }
      return x;
   }
}
