
public class BlockContractWithReturn {
   /*@ normal_behavior
     @ requires x == 2;
     @ ensures \result == -2;
     @ assignable \everything;
     @*/
   public static int main(int x) {
      return magic(x);
   }
   
   public static int magic(int x) {
      /*@ return_behavior
        @ requires x == 2;
        @ returns \result == -2;
        @ assignable \strictly_nothing;
        @*/
      {
         if (x == 2) {
            return -2;
         }
      }
      return x;
   }
}
