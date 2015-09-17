package mainpack;
public class Main {
    
    /*@ 
      @ normal_behavior
      @ ensures test1p1.Settings.x == 42;
      @*/
    public static void bla() {
        test1p1.Settings.x = 42;
    }
}