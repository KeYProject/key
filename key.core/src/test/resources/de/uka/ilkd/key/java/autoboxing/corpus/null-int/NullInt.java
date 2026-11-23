public class NullInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer a = null;
        int i = a;
        return i;
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
