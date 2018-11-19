public class Test {
    
    int a;
    int b;
    
    /*@ public normal_behavior
      @ requires a == b;
      @ requires a == 42;
      @ ensures \old(b) == 42;
      @*/
    public void test_attr() { }

    /*@ public normal_behavior
      @ requires a == b;
      @ requires a == 42;
      @ ensures \old(b) == 42;
      @*/
    public void test_arg(int a, int b) { }
}
