package mainpack;
public class Main {
    
    /*@
      @ public invariant test4p2.complex.Settings.x<100 && 10+1==11;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures a == 10 && test4p2.complex.Settings.x == 42;
      @*/
    public static void bla() {
        test4p2.complex.Settings.x = 42;
    }
}