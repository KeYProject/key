public class BlockContractTest {
   private int value;
   
   /*@ normal_behavior
     @ ensures \result == 1;
     @ assignable value;
     @*/
   public int setValueToOne() {
      {
         value = 1;
      }
      return value;
   }
}
