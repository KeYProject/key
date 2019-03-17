public class AliasedByExecution {
   private int value;
   
   /*@ normal_behavior
     @ ensures true;
     @*/
   public static int magic(AliasedByExecution a, AliasedByExecution b) {
      a.value = 2;
      if (a == b) {
         b.value = 3;
      }
      return a.value;
   }
}