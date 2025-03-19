public class Conditional{
	public int[] a;
	/*@public normal_behavior
	 @ requires \dl_noR(\dl_arrayRange(a,0,a.length-1)) && \dl_noW(\dl_arrayRange(a,0,a.length-1));
	 @ ensures \dl_noRaW(\dl_arrayRange(a,0,a.length-1)) && \dl_noWaW(\dl_arrayRange(a,0,a.length-1));
	 @ diverges true;
	 @*/
	public void arrayShift() {
		int i=0;
		/*@ loop_invariant i>=0 && i <= a.length-1 &&
		@ \dl_noRaW(\dl_arrayRange(a,0,a.length-1)) &&
		@ \dl_noWaW(\dl_arrayRange(a,0,a.length-1));
		@ decreases a.length - i;
		@ assignable a[0..a.length-2];
		@*/
		while(i < a.length - 1) {
			if(i < (a.length - 1)/2) {
				a[i]=a[i+1];
			} else {
				a[i]=1;
			}
			i++;
		}
	}
}