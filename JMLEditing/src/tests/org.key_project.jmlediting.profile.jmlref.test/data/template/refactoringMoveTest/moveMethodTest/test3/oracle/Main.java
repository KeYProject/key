package mainpack;
public class Main {
    
    /*@
      @ public invariant x==2 && test3p2.Params.go()<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures true && test3p2.Params.go() == 42 && x==2;
      @*/
    public static void bla() {
        test3p1.Settings.x = 42;
    }
}