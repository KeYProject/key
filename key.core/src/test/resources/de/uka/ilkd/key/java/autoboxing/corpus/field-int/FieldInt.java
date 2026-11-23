public class FieldInt {
    Integer f;

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public int m() {
        f = 42;
        int i = f;
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("field=" + new FieldInt().m());
    }
}
