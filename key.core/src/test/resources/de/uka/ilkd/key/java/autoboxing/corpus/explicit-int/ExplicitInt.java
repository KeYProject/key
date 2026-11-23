public class ExplicitInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = Integer.valueOf(42);
        int i = a.intValue();
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("int=" + m());
    }
}
