public class Example {
   private int value;
   
   /*@ normal_behavior
     @ ensures true;
     @*/
   public static int magic(Example a, Example b) {
      a.value = 2;
      b.value = 3;
      return a.value;
   }
}