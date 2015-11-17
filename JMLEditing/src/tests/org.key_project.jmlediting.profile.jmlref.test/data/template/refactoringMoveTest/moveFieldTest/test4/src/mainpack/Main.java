package mainpack;
public class Main {
    
    /*@
      @ public invariant x==2 && test4p2.complex.Params.x<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures true && test4p2.complex.Params.x == 42 && x==2;
      @*/
    public static void bla() {
        test4p2.complex.Params.x = 42;
    }
}