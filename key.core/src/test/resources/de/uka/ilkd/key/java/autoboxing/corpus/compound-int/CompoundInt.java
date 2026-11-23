public class CompoundInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = 42;
        a += 1;
        int i = a;
        //@ assert i == 43;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("compound=" + m());
    }
}
