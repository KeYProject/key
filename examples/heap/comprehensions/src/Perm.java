class Perm {

  int[] a;

  /*@ normal_behavior
    @ requires pIdx == 0;
    @ ensures \result == (\sum int j; 0 <= j && j < a.length; a[j]);
    @*/
  int foo() {
      int s = 0;
      /*@ maintaining s == (\sum int i; 0 <= i && i < pIdx; (int)c[i]);
        @ maintaining \invariant_for(this);
        @ decreasing a.length - pIdx;
        @ assignable pIdx;
        @*/
      while (hasNext())
          s+= a[next()];
      return s;
  }

  /*@ ghost \seq perm; // permutation on indices
    @ ghost int pIdx;
    @ invariant 0 <= pIdx && pIdx <= a.length;
    @ invariant perm.length == a.length;
    @ invariant \dl_seqNPerm(perm);
    @
    @ ghost \seq b; // a as seq
    @ invariant b == (\seq_def int i; 0; a.length; a[i]);
    @
    @ ghost \seq c; // a permuted by perm
    @ invariant \dl_seqPerm(b,c);
    @ invariant (\forall int i; 0 <= i && i < a.length;
    @               (int)c[i] == (int)b[(int)perm[i]]);
    @*/

  /*@ normal_behavior
    @ ensures \result == (pIdx < a.length);
    @ strictly_pure helper
    @*/
  boolean hasNext();

  /*@ normal_behavior
    @ requires pIdx < a.length;
    @ ensures 0 <= \result && \result < a.length;
    @ ensures \result == (int)perm[\old(pIdx)];
    @ ensures pIdx == \old(pIdx)+1;
    @ assignable pIdx;
    @*/
  int next();

}
