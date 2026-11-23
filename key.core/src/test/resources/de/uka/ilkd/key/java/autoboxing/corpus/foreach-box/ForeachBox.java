public class ForeachBox {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        int[] a = { 1, 2, 3 };
        int s = 0;
        for (Integer x : a) {
            s += x;
        }
        //@ assert s == 6;
        return s;
    }

    public static void main(String[] args) {
        System.out.println("foreachbox=" + m());
    }
}
