public class ArrayShift{
	public int[] a;
	/*@public normal_behavior
	 @ requires a.length > 10;
	 @ ensures \dl_noRaW(\dl_arrayRange(a,0,a.length-1));
	 @ diverges true;
	 @*/
	public void arrayShift() {
		// \dl_noR({(a, \dl_arr(0)}): \dl_singleton(a, \dl_arr(0))
		int i=0;
		/*@ loop_invariant i>=0 && i <= a.length-1 && 
		@ (\forall int j; j>=0 && j<i; a[j]==\old(a[j+1])) &&
		@ \dl_noRaW(\dl_arrayRange(a,0,a.length-1)) &&  \dl_noR(\dl_arrayRange(a,0,0));
		@ decreases a.length - i;
		@ assignable a[0..a.length-2];
		@*/
		while(i < a.length - 1) {
			a[i]=a[i+1];
			i++;
		}
	}
}