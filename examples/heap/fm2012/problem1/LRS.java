/** Implementation of the Longest Repeated Substring algorithm.
  * <em>FM 2012 Verification Competition, Problem 1 (part b).</em><br>
  * Together with a suffix array, LCP can be used to solve interesting text
  * problems, such as finding the longest repeated substring (LRS) in a text.<br>
  * A suffix array (for a given text) is an array of all suffixes of the
  * text. For the text [7,8,8,6], the suffix array is
  *   [[7,8,8,6],
  *      [8,8,6],
  *        [8,6],
  *          [6]]
  * <p>Typically, the suffixes are not stored explicitly as above but
  * represented as pointers into the original text. The suffixes in a suffix
  * array  are sorted in lexicographical order. This way, occurrences of
  * repeated substrings in the original text are neighbors in the suffix
  * array.</p>
  *
  * For the above, example (assuming pointers are 0-based integers), the
  * sorted suffix array is: [3,0,2,1]
  */
public class LRS {


    private static int solStart = 0;
    private static int solLength = 0;
    private static int[] a;


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
