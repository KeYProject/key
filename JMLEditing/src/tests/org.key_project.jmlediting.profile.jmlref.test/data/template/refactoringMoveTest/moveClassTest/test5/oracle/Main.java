package mainpack;
public class Main {
    
    /*@
      @ public invariant mainpack.Settings.x<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures mainpack.Settings.x == 42;
      @*/
    public static void bla() {
        mainpack.Settings.x = 42;
    }
}