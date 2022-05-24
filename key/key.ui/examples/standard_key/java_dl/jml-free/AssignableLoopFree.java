public class AssignableLoopFree {

    public static int field;
    
    /*@ public normal_behavior
      @ ensures field == 21; */
    void foo() {
        field = 0;
        /*@ loop_invariant 0 <= i <= 21;
          @ loop_invariant field == i;
          @ decreases 21 - i;
          @ assignable field;
          @ */
        for (int i = 0; i < 21; ++i) { ++field; }
        
        /*@ loop_invariant 0 <= j <= 21;
          @ decreases 21 - j;
          @ assignable field;
          @ assignable_free \nothing;
          @ */
        for (int j = 0; j < 21; ++j) { ++field; }
        
        /*@ loop_invariant 0 <= k <= 21;
          @ decreases 21 - k;
          @ assignable_free \nothing;
          @ */
        for (int k = 0; k < 21; ++k) { ++field; }
    }
}
