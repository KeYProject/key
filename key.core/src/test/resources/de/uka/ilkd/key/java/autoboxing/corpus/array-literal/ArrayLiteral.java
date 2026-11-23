public class ArrayLiteral {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer[] xs = { 1, 2 };
        int i = xs[1];
        //@ assert i == 2;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("array=" + m());
    }
}
