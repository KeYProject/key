public class ArgInt {
    static int id(Integer x) {
        return x;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        int i = id(42);
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("arg=" + m());
    }
}
