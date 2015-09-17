package mainpack;
public class Main {
    
    /*@ 
      @ normal_behavior
      @ ensures mainpack.Main.x == 42;
      @*/
    public static void bla() {
        mainpack.Main.x = 42;
    }

    public static int x;
}