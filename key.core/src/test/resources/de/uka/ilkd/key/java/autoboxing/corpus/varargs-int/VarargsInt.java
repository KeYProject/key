public class VarargsInt {
    static int first(Integer... xs) {
        return xs[0];
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        int i = first(42);
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("varargs=" + m());
    }
}
