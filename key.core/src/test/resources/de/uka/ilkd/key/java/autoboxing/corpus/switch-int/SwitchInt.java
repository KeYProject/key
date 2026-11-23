public class SwitchInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 2;
        int r = 0;
        switch (a) {
            case 1: r = 1; break;
            case 2: r = 2; break;
            default: r = 0; break;
        }
        //@ assert r == 2;
        return r;
    }

    public static void main(String[] args) {
        System.out.println("switch=" + m());
    }
}
