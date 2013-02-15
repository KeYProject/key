final class PrefixSumRec {

    private final int[] a;
    
    //@ invariant a.length > 0;
    //@ invariant isPow2(a.length);
    //@ accessible \inv: \singleton(a);
    
    //@ axiom lemma();
    
    /*@ normal_behavior
      @ ensures (\forall int x, y; even(x); even(x+y) == even(y));
      @ accessible \nothing;
      @ strictly_pure helper
      @*/
    private static boolean lemma() { return true; }

    PrefixSumRec(int [] a) {
	this.a = a;
    }

    /*@ public normal_behavior
      @   requires x > 0;
      @   ensures \result ==> ((even(x)  && isPow2(div2(x))) <=!=> x == 1);
      @   ensures \result == (\exists int b; 0 <= b;
      @                     x == (\product int i; 0 <= i && i < b; 2));
      @   measured_by x;
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static boolean isPow2(int x){
      if (x==1) 
          return true;
      else if (x % 2 != 0 ) 
          return false;
      else 
          return isPow2(x/2);
    } // proven with interaction (requires induction)

    /*@ normal_behavior
      @   requires x > 0;
      @   requires even(x);
      @   ensures \result*2 == x;
      @   ensures \result < x;
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static int div2 (int x) {
        return x/2;
    }
    
    /*@ normal_behavior
      @   ensures \result == (\exists int y; y*2 == x);
      @   ensures \result != (\exists int y; y*2 == x+1);
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static boolean even (int x) {
        return x%2==0;
    }

    //@ strictly_pure
    private /*@ helper @*/ static int leftMost(int left, int right) {
	return 2*left - right + 1;
    }

    /*@ public normal_behavior
      @   requires right > left;
      @   requires leftMost(left, right) >= 0;
      @   requires right < a.length;
      @   requires isPow2(right-left);
      @   requires !even(right);
      @   requires !even(left) || right-left==1;
      @   ensures (\forall int k; leftMost(left, right) <= k && k <= right && !even(k); 
      @            a[k] == (\sum int i; leftMost(left, right) <= i && i < k+1; \old(a[i])));
      @   ensures !(\exists int k; leftMost(left, right) <= k && k <= right && even(k);
      @             a[k] != \old(a[k]));
      @   measured_by right - left + 1;
      @   assignable \infinite_union(int k; 
      @                  (2*left-right+1 <= k && k <= right && !even(k)) ?
      @                      \singleton(a[k]): \empty);
      @*/
    public void upsweep(int left, int right) {
        int space = right - left;
        if (space > 1) {
            upsweep(left-div2(space),left);
            upsweep(right-div2(space),right);
        }
        a[right] = a[left]+a[right];
    }

    /*@ normal_behavior
      @   requires right > left;
      @   requires leftMost(left, right) >= 0;
      @   requires right < a.length;
      @   requires isPow2(right-left);
      @   requires !even(right);
      @   requires !even(left) || right-left==1;
      @   ensures (\forall int k; leftMost(left, right) <= k && k <= right && even(k);
      @                        a[k] == (\sum int i; leftMost(left,right) <= i && i < k+1;
      @                        ((isPow2(k-i+1) && k-i != 1) || i == right)? \old(a[i]) : 0));
      @   ensures (\forall int k; leftMost(left, right) <= k && k <= right && !even(k); 
      @                        a[k] == (\sum int i; leftMost(left, right) <= i && i < k+1; 
      @                        (isPow2(k-i) || k == i)? \old(a[i]) : 0 ));
      @   measured_by right - left + 1;
      @   assignable a[*];
      @*/
    public void downsweep(int left, int right) {
        int tmp = a[right];
        a[right] = a[right] + a[left];
        a[left] = tmp;
        int space = right - left;
        if (space > 1) {
            downsweep(left-div2(space),left);
            downsweep(right-div2(space),right);
        }
    }
    
    /*@ normal_behavior
      @   requires \invariant_for(p);
      @   ensures (\forall int i; 0 <= i && i < p.a.length;
      @             p.a[i] == (\sum int j; 0 <= j && j < i;
      @                           \old(p.a[i])));
      @*/
    public static void main( PrefixSumRec p ) {
        final int l = div2(p.a.length)-1;
        final int r = p.a.length-1;
        p.upsweep(l, r);
        p.a[r] = 0;
        p.downsweep(l, r);
    }
}
