package mainpack;

import test1p2.Settings;

public class Main {
    
    /*@
      @ public invariant Settings.x<100;
      @*/
    int x=0;
    
    /*@ 
      @ normal_behavior
      @ ensures Settings.x == 42;
      @*/
    public static void bla() {
        Settings.x = 42;
    }
}