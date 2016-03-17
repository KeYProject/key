public class LoopInvariantExample {
   public /*@ non_null @*/ int[] a;

   /*@ normal_behavior
     @ ensures (\forall int i; i >= 0 && i < a.length; a[i] == 1);
     @*/
   public void setAllToOne() {
      int i = 0;
       
      /*@ loop_invariant i >= 0 && i <= a.length; 
        @ loop_invariant (\forall int j; j >= 0 && j < i; a[j] == 1);
        @ decreases a.length - i;
        @ assignable i, a[*];
        @*/
      while (i < a.length) {
         a[i] = 1;
         i++;
      }
   }
}