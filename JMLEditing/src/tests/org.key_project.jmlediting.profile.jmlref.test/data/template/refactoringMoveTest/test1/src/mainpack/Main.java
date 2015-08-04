public class Main {
    
    /*@
      @ public invariant test.Settings.x<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures test.Settings.x == 42;
      @*/
    public static void bla() {
        test.Settings.x = 42;
    }
}