public class AssignableFree {

    public static int field;
    public static Object obj;
    
    /*@ public normal_behavior
      @ ensures field == 21; */
    void foo() {
        foo0();
        foo1();
        foo2();
        foo3();
    }

    /*@ public normal_behavior
      @ ensures field == 21; 
      @ assignable \strictly_nothing;
      @ assignable_free field;
      @*/
    void foo0() {
        field = 21;
        new Object();
    }

    /*@ public normal_behavior
      @ ensures field == 21; 
      @ assignable obj;
      @ assignable_free field;
      @*/
    void foo1() {
        field = 21;
        obj = new Object();
    }

    /*@ public normal_behavior
      @ ensures true; 
      @ assignable \strictly_nothing;
      @ assignable_free \nothing;
      @*/
    void foo2() {
        new Object();
    }

    /*@ public normal_behavior
      @ ensures true;
      @ assignable \strictly_nothing;
      @ assignable_free field;
      @*/
    void foo3() {
        field = 42;
        obj = new Object();
    }
}
