package mainpack;
public class Main {
    
    /*@
      @ public invariant test1p2.Params.go()<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures test1p2.Params.go() == 42;
      @*/
    public static void bla() {
        test1p1.Settings.x = 42;
    }
}