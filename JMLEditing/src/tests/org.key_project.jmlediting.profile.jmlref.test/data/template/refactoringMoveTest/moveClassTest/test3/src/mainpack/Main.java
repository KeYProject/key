package mainpack;
public class Main {
    
    /*@
      @ public invariant test3p1.Settings.x<100 && 10+1==11 || test3p1.Settings.x == 42;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures a == 10 && test3p1.Settings.x == 42;
      @*/
    public static void bla() {
        test3p1.Settings.x = 42;
    }
}