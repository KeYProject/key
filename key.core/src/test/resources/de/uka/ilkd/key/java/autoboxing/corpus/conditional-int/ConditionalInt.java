public class ConditionalInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        boolean f = true;
        int i = f ? a : 0;
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("cond=" + m());
    }
}
