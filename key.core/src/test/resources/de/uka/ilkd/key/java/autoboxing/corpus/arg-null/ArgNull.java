public class ArgNull {
    static int id(int x) {
        return x;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = null;
        return id(a);
    }

    public static void main(String[] args) {
        try {
            m();
            System.out.println("no-npe");
        } catch (NullPointerException e) {
            System.out.println("npe");
        }
    }
}
