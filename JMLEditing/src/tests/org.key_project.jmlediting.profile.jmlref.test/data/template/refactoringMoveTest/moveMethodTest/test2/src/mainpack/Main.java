package mainpack;
public class Main {
    
    /*@
      @ public invariant test2p1.Settings.go()<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures test2p1.Settings.go() == 42;
      @*/
    public static void bla() {
        test2p1.Settings.x = 42;
    }
}