public class Maximum {

    /*@ public normal_behaviour
      @  requires array.length > 0;
      @  ensures 0 <= \result && \result < array.length;
      @  ensures (\forall int i; 0 <= i && i < array.length; 
      @               array[i] <= array[\result]);
      @  assignable \strictly_nothing;
      @*/
    public static int maxIndex(int[] array) {

        int x = 0;
        int y = array.length - 1;

        /*@ loop_invariant 0 <= x && x <= y && y < array.length;
          @ loop_invariant (\forall int j; 
          @   0 <= j && j <= x || y <= j && j < array.length;
          @   array[j] <= array[x] || array[j] <= array[y]);
          @ decreases y - x;
          @ assignable \strictly_nothing;
          @*/
        while(x != y) {
            if(array[x] <= array[y]) {
                x++;
            } else {
                y--;
            }
        }

        return x;
    }
}
