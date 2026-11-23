public class ValueOfIdentity {
    /*@ normal_behavior
      @ requires true;
      @ ensures Integer.valueOf(42) == Integer.valueOf(42);
      @*/
    public static void m() {
    }

    public static void main(String[] args) {
        System.out.println("identity42=" + (Integer.valueOf(42) == Integer.valueOf(42)));
    }
}
