public class AssignableFree {

    public static int field;
    
    /*@ public normal_behavior
      @ ensures field == 21; */
    void foo() {
        foo0();
        foo1();
    }

    /*@ public normal_behavior
      @ ensures field == 21; 
      @ assignable field; */
    void foo0() {
        field = 21;
    }

    /*@ public normal_behavior
      @ ensures true; 
      @ assignable field;
      @ assignable_free \nothing; */
    void foo1() {
        field = 42;
    }
}
