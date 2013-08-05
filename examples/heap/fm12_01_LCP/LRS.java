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


    private int solStart = 0;
    private int solLength = 0;
    private final int[] a;


    /*@ normal_behavior
      @ requires a.length >= 2;
      @ requires (\exists int i,j; 0 <= i && i < j && j < a.length; a[i] == a[j]);
      @ requires solStart == 0 && solLength == 0;
      @ ensures (\exists int i; 0 <= i && i < a.length && i != solStart;
      @         (\forall int j; 0 <= j && j < solLength; 
      @              a[solStart+j] == a[i+j]))
      @         // there is a repeated substring
      @         || solLength == 0; // or not
      @ ensures !(\exists int i,k; 0 <= i && i < k && k < a.length;
      @           (\forall int j; 0 <= j && j < solLength+1; a[k+j] == a[i+j]));
      @         // and it is maximal
      @*/
    public void doLRS() {
        SuffixArray sa = new SuffixArray(a);

        /*@ maintaining \invariant_for(sa);
          @ maintaining 0 <= solStart && solStart < a.length;
          @ maintaining 0 <= solLength && solLength < a.length;
          @ maintaining solStart+solLength-1 < a.length;
          @ maintaining 0 < l && l <= a.length;
          @ maintaining (\forall int i; sa.suffixes[i]+1 == solStart;
          @                 (\forall int j; 0 <= j && j < solLength; 
          @                     a[solStart+j] == a[sa.suffixes[i]+j]))
          @             || solLength == 0;
          @ maintaining !(\exists int i,k; 0 <= i && i< k && k < l;
          @                 (\forall int j; 0 <= j && j < solLength+1; 
          @                      a[sa.suffixes[k]+j] == a[sa.suffixes[i]+j]));
          @ decreasing a.length-l;
          @ assignable solStart,solLength;
          @*/
        for (int l=1; l < a.length; l++) {
            int length = sa.lcp(l);
            if (length > solLength) {
                solStart = sa.suffixes[l];
                solLength = length;
            }
        }
    }

}


//Based on code by Robert Sedgewick and Kevin Wayne.
