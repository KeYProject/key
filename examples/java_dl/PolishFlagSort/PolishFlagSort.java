public class PolishFlagSort {
    public static final int RED = 0;
    public static final int WHITE = 1;    

    /*@
      @ public normal_behavior
      @    requires ar != null &&
      @             (\forall int i; 0 <= i && i < ar.length;
      @              ar[i] == RED || ar[i] == WHITE);
      @    ensures (\forall int I, J; 0 <= I && I < J && J < ar.length;
      @             ar[I] <= ar[J]);
      @    assignable ar[*];
      @*/
    public static void sort ( int[] ar ) {
	if (ar.length <= 0) return;

	int i = 0; int j = ar.length;

	/*@ loop_invariant 0 <= i && i <= j && j <= ar.length
	  @                &&
	  @                (\forall int i; 0 <= i && i < ar.length;
	  @                ar[i] == RED || ar[i] == WHITE)
	  @                &&
	  @                (\forall int I; 0 <= I && I < i; ar[I] == RED)
	  @                &&
	  @                (\forall int J; j <= J && J < ar.length;
	  @                 ar[J] == WHITE);
	  @ assignable ar[*], i, j;
	  @ decreases j - i;
	  @*/
	while (i != j) {
	    if (ar[i]==RED) {
		++i;
	    } else {
		--j;
		final int t = ar[i];
		ar[i] = ar[j];
		ar[j] = t;
	    }
	}
    }
}
