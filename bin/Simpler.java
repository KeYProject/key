public class Simpler {

    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int add(int x, int y, int z) {
        /*@ requires x >= 0 && y >= 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        /*@ requires x < 0 && y < 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            z = x + y;
        }
        return z;
    }
    
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int loop(int x, int y, int z) {
        /*@ loop_invariant z == x + y;
          @ decreases x;
          @ assignable \nothing;
          @*/
        while (true) {
            z = x + y;
        }
        /*@ requires x < 0 && y < 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            z = x + y;
        }
        return z;
    }
    
    /*@ requires x >= 0 && y >= 0;
      @ ensures \result == x + y;
      @ diverges false;
      @ signals_only \nothing;
      @ assignable \nothing;
      @*/
    public int addWithJump(int x, int y, int z) {
        /*@ requires x >= 0 && y >= 0;
          @ ensures z == x + y;
          @ diverges false;
          @ signals_only \nothing;
          @ assignable \nothing;
          @*/
        {
            label: {
                z = x + y;
                break label;
            }
        }
        return z;
    }

}