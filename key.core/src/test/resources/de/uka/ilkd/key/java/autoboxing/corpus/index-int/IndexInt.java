public class IndexInt {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer idx = 1;
        int[] values = new int[] { 5, 6, 7 };
        int x = values[idx];
        //@ assert x == 6;
        return x;
    }

    public static void main(String[] args) {
        System.out.println("index=" + m());
    }
}
