/**
 * Tests that \old() works in jml assert statements
 * by incrementing diffrent kinds of fields.
 */
class Inc {
    //@ ghost int i;
    int j = 0;

    /*@ normal_behavior
      @ ensures \result == \old(a) + 1;
      @ assignable \strictly_nothing;
      @*/
    int inc_parameter(int a) {
        a = a + 1;
        //@assert a == \old(a) + 1;
        return a;
    }

    /*@ normal_behavior
      @ ensures j == \old(j) + 1;
      @ assignable j;
      @*/
    void inc_field() {
        j = j + 1;
        //@ assert j == \old(j) + 1;
    }

    /*@ normal_behavior
      @ ensures i == \old(i) + 1;
      @ assignable i;
      @*/
    void inc_ghost_field() {
        //@set i = i + 1;
        //@assert i == \old(i) + 1;
    }

    /*@ normal_behavior
      @ ensures inc.j == \old(inc.j) + 1;
      @ assignable inc.j;
      @*/
    void inc_parameter_field(Inc inc) {
        inc.j = inc.j + 1;
        //@ assert inc.j == \old(inc.j) + 1;
    }
}
