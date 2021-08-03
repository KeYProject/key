package java.lang;

public final class Math {
    
    private Math() {}
    
    /*@ public normal_behavior
      @ requires y != 0;
      @ ensures (\exists int r; r * y + \result == x);
      @ ensures y < 0 ==> (0 >= \result && \result > y);
      @ ensures y > 0 ==> (0 <= \result && \result < y);
      @ assignable \strictly_nothing;
      @*/
    public static int floorMod(int x, int y);
}
