

public class LRS {


    private static int solStart = 0;
    private static int solLength = 0;
    private static int[] a;

/*
    public static void main(String[] args) {
        a = new int[args.length];
        for (int i=0; i<args.length; i++) {
            a[i]=Integer.parseInt(args[i]);
        }
        doLRS();
        System.out.println(solStart+"->"+solLength);
    }
*/


    /*@ normal_behavior
      @ requires a != null;
      @ requires solStart == 0 && solLength == 0;
      @*/
    public static void doLRS() {
        SuffixArray sa = new SuffixArray(a);

        /*@ maintaining \invariant_for(sa);
          @ decreasing a.length-i;
          @ assignable solStart,solLength;
          @*/
        for (int i=1; i < a.length; i++) {
            int length = sa.lcp(i);
            if (length > solLength) {
                solStart = sa.select(i);
                solLength = length;
            }
        }
    }

}


//Based on code by Robert Sedgewick and Kevin Wayne.
