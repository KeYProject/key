public class ArrayStore {
    /*@ normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int m() {
        Integer[] xs = new Integer[2];
        xs[0] = 42;
        int i = xs[0];
        //@ assert i == 42;
        return i;
    }

    public static void main(String[] args) {
        System.out.println("store=" + m());
    }
}
