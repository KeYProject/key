final class PrefixSumRec {

    private final int[] a;
    
    //@ invariant a.length > 0;
    //@ invariant isPow2(a.length);
    //@ accessible \inv: \singleton(a);

    PrefixSumRec(int [] a) {
	this.a = a;
    }

    /*@ public normal_behavior
      @  requires x > 0;
      @  ensures \result ==> ((x % 2 == 0  && isPow2(x/2)) <=!=> x == 1);
      @  ensures \result == (\exists int b; 0 <= b;
      @                     x == (\product int i; 0 <= i && i < b; 2));
      @  measured_by x;
      @  strictly_pure helper
      @*/
    private boolean isPow2(int x){
      if (x==1) 
          return true;
      else if (x % 2 != 0 ) 
          return false;
      else 
          return isPow2(x/2);
    } // proven with interaction (requires induction)

    /*@ public normal_behavior
      @   requires right > left;
      @   requires 2*left-right+1 >= 0;
      @   requires (2*left-right+1)%2 == 0;
      @   requires (left+1)%2 == 0;
      @   requires right < a.length;
      @   requires isPow2(right-left);
      @   ensures (\forall int k; 2*left-right < k && k <= right && k%2 == 1; 
      @            a[k] == (\sum int i; 2*left-right+1 <= i && i < k+1; \old(a[i])));
      @   ensures !(\exists int k; 2*left-right < k && k <= right && k%2 == 1;
      @             a[k] != \old(a[k]));
      @   measured_by right - left + 1;
      @   assignable a[*];
      @*/
    public void upsweep(int left, int right) {
        int space = right - left;
        if (space > 1) {
            upsweep(left-space/2,left);
            upsweep(right-space/2,right);
        }
        a[right] = a[left]+a[right];
    }
    

    public void downsweep(int left, int right) {
        int tmp = a[right];
        a[right] = a[right] + a[left];
        a[left] = tmp;
        if (right > left+1) {
            int space = right - left;
            downsweep(left-space/2,left);
            downsweep(right-space/2,right);
        }
    
    }
    
    /*@ normal_behavior
      @   requires \invariant_for(p);
      @   ensures (\forall int i; 0 <= i && i < p.a.length;
      @             p.a[i] == (\sum int j; 0 <= j && j < i;
      @                           \old(p.a[i])));
      @*/
    public static void main( PrefixSumRec p ) {
        final int l = (p.a.length/2)-1;
        final int r = p.a.length-1;
        p.upsweep(l, r);
        p.a[r] = 0;
        p.downsweep(l, r);
    }
}
