
public class BlockContractThisTest {
   private int x;

   private int y;

   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/   
   public int main(BlockContractThisTest a) {
      return a.magic();
   }
   
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public int magic() {
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
