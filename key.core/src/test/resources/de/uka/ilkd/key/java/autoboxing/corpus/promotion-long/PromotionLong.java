public class PromotionLong {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static long m() {
        Integer a = 42;
        long v = a + 1L;
        //@ assert v == 43L;
        return v;
    }

    public static void main(String[] args) {
        System.out.println("long=" + m());
    }
}
