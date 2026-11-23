public class UniformLong {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static long m() {
        Long a = 42L;
        long i = a;
        //@ assert i == 42L;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("long=" + m());
    }
}
