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
    
    // This contract contains an intentional mistake.
    /*@ public normal_behavior
      @ requires x <= 0;
      @ ensures \result > 0;
      @*/
    public int very_simple(int x){
        if(x > 0) {
            x--;
        } else {
            x++;
        }
        return ++x;
    }
}
