public class BlockContractTest {
   private int value;
   
   /*@ normal_behavior
     @ ensures \result == 1;
     @ assignable value;
     @*/
   public int setValueToOne() {
      /*@ normal_behavior
        @ requires true;
        @ ensures value == 1;
        @ assignable value; 
        @*/
      {
         value = 1;; // TODO:The double semicolons are needed, because block contracts are not pretty printed by ProofMetaReferencesPrettyPrinter and consequently no change will be detected by KeY Resources at the moment.
      }
      return value;
   }
}
