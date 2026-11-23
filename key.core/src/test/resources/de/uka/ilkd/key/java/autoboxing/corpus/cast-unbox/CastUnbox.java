public class CastUnbox {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        int i = (int) a;
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("cast=" + m());
    }
}
