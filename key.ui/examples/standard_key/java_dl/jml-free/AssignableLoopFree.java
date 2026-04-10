public class AssignableLoopFree {

    public static int field;
    public static Object obj;
    
    /*@ public normal_behavior
      @ ensures field == 21; */
    void foo() {
        field = 0;
        
        /*@ loop_invariant 0 <= j <= 21;
          @ decreases 21 - j;
          @ assignable \strictly_nothing;
          @ assignable_free \nothing;
          @ */
        for (int j = 0; j < 21; ++j) { new Object(); }
        
        /*@ loop_invariant 0 <= i <= 21;
          @ loop_invariant field == i;
          @ decreases 21 - i;
          @ assignable \strictly_nothing;
          @ assignable_free field;
          @ */
        for (int i = 0; i < 21; ++i) { ++field; new Object(); }
    }
}
