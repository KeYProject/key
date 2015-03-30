public class MethodContract {
   private int h1, h2;
   public int l;

   /*@ public normal_behavior
     @ requires x>=0 && y>0;
     @ ensures (\exists int k; ((y*k + \result) == x));
     @*/
   private int mod(int x, int y) {
      if (x <= y)
         return x;
      else
         return mod(x - y, y);
   }

   public void magic(int m) {
      if (m > 10)
         l = mod(h1, h2);
      else
         l = 6;
   }
}