public class ForeachUnbox {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer[] a = { 1, 2, 3 };
        int s = 0;
        for (int x : a) {
            s += x;
        }
        //@ assert s == 6;
        return s;
    }

    public static void main(String[] args) {
        System.out.println("foreachunbox=" + m());
    }
}
