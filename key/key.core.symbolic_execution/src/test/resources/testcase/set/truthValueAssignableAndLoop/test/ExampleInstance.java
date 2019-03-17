public class ExampleInstance {
   private int x;
   
    /*@ normal_behavior
      @ ensures \result ==0;
      @ assignable \nothing;
      @*/
    public int magic() {
       if (x < 0)  {
          throw new RuntimeException("x < 0");
       }
       /*@ loop_invariant x >= 0;
         @ decreasing x;
         @ assignable x;
         @*/
       while (x > 0) {
    	   x = decrease(x);
       }
       return x;
    }

   /*@ normal_behavior
     @ ensures \result == x - 2;
     @ assignable \nothing;
     @*/
   private static int decrease(int x) {
      return x - 2;
   }
}
