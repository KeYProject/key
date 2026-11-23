public class ReturnInt {
    static Integer box() {
        return 42;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        int i = box();
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("return=" + m());
    }
}
