public class LoopInvArrayExample {
   public int[] a;

   /*@ public normal_behavior
     @ requires a != null;
     @ ensures (\forall int x; x >= 0 && x < a.length; a[x] == 1);
     @ diverges true;
     @*/
   public void setAllToOne() {
      int i = 0;
      
      /*@ loop_invariant
        @   i >= 0 && i <= a.length &&
                  @     (\forall int x; x >= 0 && x < i; a[x] == 1);
        @*/
      while (i < a.length) {
         a[i] = 1;
         i++;
      }
   }
}
