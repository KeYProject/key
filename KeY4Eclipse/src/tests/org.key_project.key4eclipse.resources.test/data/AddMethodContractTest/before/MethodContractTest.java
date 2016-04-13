public class MethodContractTest {
   private int value;
   
   /*@ normal_behavior
     @ ensures \result == 1;
     @ assignable value;
     @*/
   public int setValueToOne() {
      helpingMethod();
      return value;
   }
   
   public void helpingMethod();
}
