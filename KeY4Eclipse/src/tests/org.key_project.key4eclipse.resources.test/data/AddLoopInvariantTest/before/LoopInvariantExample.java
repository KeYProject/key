public class LoopInvariantExample {
   public /*@ non_null @*/ int[] a;

   /*@ normal_behavior
     @ ensures (\forall int i; i >= 0 && i < a.length; a[i] == 1);
     @*/
   public void setAllToOne() {
      int i = 0;
       
      while (i < a.length) {
         a[i] = 1;
         i++;
      }
   }
}