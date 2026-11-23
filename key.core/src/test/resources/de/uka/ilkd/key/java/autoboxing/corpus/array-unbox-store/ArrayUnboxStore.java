public class ArrayUnboxStore {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        int[] a = new int[1];
        Integer x = 42;
        a[0] = x;
        //@ assert a[0] == 42;
        return a[0];
    }

    public static void main(String[] args) {
        System.out.println("unboxstore=" + m());
    }
}
