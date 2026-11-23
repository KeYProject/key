public class NumberInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static void m() {
        Number n = 42;
        //@ assert n != null;
    }

    public static void main(String[] args) {
        m();
        System.out.println("number=nonnull");
    }
}
