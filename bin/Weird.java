public class Weird {
    
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @
      @ also
      @
      @ requires x < 0 && y < 0;
      @ ensures \result == x * y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @
      @ also
      @
      @ requires x < 0 && y > 0;
      @ ensures \result == x / y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int add(int x, int y) {
        int z = 0;
        label: {
            /*@ requires x >= 0 && y >= 0;
              @ ensures z == x + y;
              @ diverges false;
              @ signals_only \nothing;
              @ assignable \nothing;
              @
              @ also
              @
              @ requires x < 0 && y < 0;
              @ returns \result == x * y;
              @ diverges false;
              @ signals_only \nothing;
              @ assignable \nothing;
              @
              @ also
              @
              @ requires x < 0 && y > 0;
              @ breaks (label) z == x / y;
              @ diverges false;
              @ signals_only \nothing;
              @ assignable \nothing;
              @*/
           {
               if (x >= 0 && y >= 0) {
                   z = x + y;
               }
               if (x < 0 && y < 0) {
                   return x * y;
               }
               while (true) {
                   if (x < 0 && y >= 0) {
                       z = x / y;
                       break label;
                   }
                   else {
                       continue;
                   }
               }
           }
        }
        return z;
    }
    
}