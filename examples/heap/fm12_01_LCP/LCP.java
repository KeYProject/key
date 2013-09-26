/** Contains an implementation for the Longest Common Prefix algorithm.
  * <em>FM 2012 Verification Competition, Problem 1 (part a).</em><br>
  * Longest Common Prefix (LCP) is an algorithm used for text querying. In
  * the following, we model text as an integer array. <ul>
  * <li> Input:  an integer array a, and two indices x and y into this array
  * <li> Output: length of the longest common prefix of the subarrays of a
  *     starting at x and y respectively.</ul>
  * @author bruns, woj
  */
final class LCP {


/*@ normal_behavior
  @ requires 0 <= x && x < a.length;
  @ requires 0 <= y && y < a.length;
  @ requires x != y;
  @ ensures 0 <= \result;
  @ ensures \result <= a.length - x;
  @ ensures \result <= a.length - y;
  @ ensures (\forall int i; 0 <= i && i < \result;//ß\label{lst:lcp-post-ex1}ß
  @                         a[x+i] == a[y+i] );//ß\label{lst:lcp-post-ex2}ß
  @ ensures a[x+\result] != a[y+\result]//ß\label{lst:lcp-post-max-start}ß
  @             || \result == a.length-x 
  @             || \result == a.length-y;//ß\label{lst:lcp-post-max-end}ß
  @ strictly_pure @*/
static int lcp(int[] a, int x, int y) {
    int l = 0;
    /*@ maintaining 0 <= l && l+x <= a.length//ß\label{lst:lcp-inv1-start}ß
      @             && l+y <= a.length && x!=y;//ß\label{lst:lcp-inv1-end}ß
      @ maintaining (\forall int z; 0 <= z && z < l;//ß\label{lst:lcp-inv2-start}ß 
      @                          a[x+z] == a[y+z] );//ß\label{lst:lcp-inv2-end}ß
      @ decreasing a.length-l; //ß\label{lst:lcp-variant}ß
      @ assignable \strictly_nothing; @*/ //ß\label{lst:lcp-loopframe}ß     
    while (x+l<a.length && y+l<a.length 
             && a[x+l]==a[y+l]) l++;
    return l;
}
}
