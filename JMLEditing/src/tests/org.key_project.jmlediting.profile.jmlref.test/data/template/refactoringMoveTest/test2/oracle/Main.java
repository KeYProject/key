package mainpack;
public class Main {
    /*@
      @ public invariant test2p2.complex.Settings.x<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures test2p2.complex.Settings.x == 42;
      @*/
    public static void bla() {
        test2p2.complex.Settings.x = 42;
    }
}