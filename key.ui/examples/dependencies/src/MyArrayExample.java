public class MyArrayExample{
	public int[] a;
	/*@public normal_behavior
	 @ ensures (\forall int x; x>=0 && x<a.length; a[x]==1);
	 @ diverges true;
	 @*/
	public void m() {
		int i=0;
		/*@loop_invariant
		 @ i>=0 && i<=a.length &&
		 @  (\forall int x; x>=0 && x>i; a[x]==1);
		 @ 	assignable a[*];
		 @*/
		while(i<a.length) {
			a[i]=1;
			i++;
		}
	}
}