public class VariableMethodContractTest {
   public int l; 
   public int l2;
   
   public void findMax(){
      l2 = 0;
      l = max(this);
   }
   
   /*@ requires true;
     @ ensures m.l2 == 42;
     @ assignable m.l2;
     @*/
   public static int max(VariableMethodContractTest m){
      return 0;
   }
}