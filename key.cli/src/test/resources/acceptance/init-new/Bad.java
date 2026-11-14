public class Bad {
    /*@ public normal_behavior
      @   ensures true;
      @*/
    public int m() {
        int[][] a = new int[][]{{1,2}};
        return 0;
    }
}
