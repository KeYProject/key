public class ExplicitLong {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static long m() {
        Long a = Long.valueOf(42L);
        long i = a.longValue();
        //@ assert i == 42L;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("long=" + m());
    }
}
