/** From the second KeY book.
 * https://link.springer.com/chapter/10.1007/978-3-319-49812-6_12
 * Listing 12.1
 */
public class ArrayUtils {
    /*@ public normal_behavior
      @ ensures (\forall int i; 0<=i && i<a.length; a[i]==b[i]);
      @*/
    public void arrCopy(int[] a, int[] b) {
        for (int i = 0; i < a.length; i++) {
            b[i] = a[i];
        }
    }
}