package pkgB;

public class A {
    //@ public static invariant COUNT >= 0;
    public static int COUNT;

    /*@ public normal_behavior
        ensures \result == (COUNT == \old(COUNT) + 1);
        model two_state static boolean monInc();
     */
    
    /*@ public normal_behavior
      @ ensures monInc();
      @*/
    public static void inc() {
        COUNT++;
    }
}