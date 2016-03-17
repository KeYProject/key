public class MethodContractTest {
   private int value;
   
   /*@ normal_behavior
     @ ensures \result == 1;
     @ assignable value;
     @*/
   public int setValueToOne() {
      helpingMethod();; // The double semicolon is needed to detect a change in this method.
      return value;
   }
   
   /*@ normal_behavior
     @ ensures value == 1;
     @ assignable value;
     @*/
   public void helpingMethod();
}
