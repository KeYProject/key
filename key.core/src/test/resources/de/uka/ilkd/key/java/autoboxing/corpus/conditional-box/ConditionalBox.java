public class ConditionalBox {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        boolean f = false;
        Integer a = f ? 1 : Integer.valueOf(42);
        int i = a;
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("box=" + m());
    }
}
