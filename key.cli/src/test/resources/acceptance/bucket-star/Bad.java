public class Bad {
    public int[][] bucketData;

    /*@ public normal_behavior
      @   assignable bucketData[*][*];
      @   ensures true;
      @*/
    public void set() {
    }
}
