public class Bad {
    /*@ public normal_behavior
      @   ensures true;
      @*/
    public int m(int n) {
        int[][] a = new int[n][];
        return 0;
    }
}
