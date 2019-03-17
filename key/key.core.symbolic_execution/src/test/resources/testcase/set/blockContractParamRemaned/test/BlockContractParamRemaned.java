
public class BlockContractParamRemaned {
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main(int x, int y) {
      return magic(x, y);
   }
   
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int magic(int x, int y) {
      x = 2;
      y = 3;
      /*@ normal_behavior
        @ requires x == 2;
        @ ensures x == -2;
        @ assignable x;
        @*/
      {
         x = -2;
      }
      return x;
   }
}
