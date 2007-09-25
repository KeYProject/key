public class ASEPrim {
    int[][] g;

  /*@ normal_behavior
    @  ensures true;
    @*/
  public static void main(String[] args) {
    Object[] o = new Object[3];
    o[0] = new byte[3][2];
    ((Object[])(o[0]))[0] = (Object)new int[2];
  }
}
                     