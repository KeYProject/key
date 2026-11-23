public class PromotionInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        int i = a + 1;
        //@ assert i == 43;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("promotion=" + m());
    }
}
