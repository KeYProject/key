public class SimpleMin {

    /*@ public normal_behavior
          requires System.out != null;
          ensures a >= b ==> \result == b;
          ensures a <  b ==> \result == a;
          assignable \strictly_nothing;
      @*/
    public static int min(int a, int b) {
        int m = a;
        if (b < m) m = b;
        a = b = 0;
        System.out.println("123456");
        return m;
    }
}
