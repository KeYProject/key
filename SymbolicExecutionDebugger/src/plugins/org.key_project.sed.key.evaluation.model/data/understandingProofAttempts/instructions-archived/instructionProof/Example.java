public class Example {
   protected int value;

    /*@ normal_behavior
      @ ensures f.value == 0;
      @ ensures s.value == \old(s.value);
      @ assignable f.value;
      @*/
    public static void magic(int x,
               /*@ non_null @*/Example f,
               /*@ non_null @*/Example s)
               throws Exception {
       if (x < 0) {
          throw new Exception("x < 0");
       }
       /*@ loop_invariant x >= 0;
         @ decreasing x;
         @ assignable x;
         @*/
       while (x > 0)
    	   x = decrease(x);
       f.value = x;
    }

   /*@ normal_behavior
     @ ensures \result == x - 2;
     @ assignable \nothing;
     @*/
   private static int decrease(int x) {
      return x - 2;
   }
}