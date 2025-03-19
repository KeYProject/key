package de.uka.ilkd.key.loopinvgen.Examples;

public class arrShift {
	int a[];
	int i = 0;
//	int n = a.length;
	/*@
	 @ public normal_behavior
     @ requires true;
	 @ ensures true;
	 @*/
	public void func(int n) {
		/*@ loop_invariant
		 @ i>=0 && i<n;
		 @ decreases n-i;
		 @ assignable a[0..n-1];
		 @*/
		while (i < n) {
			a[i] = a[i+1];
			i++;
		}

	}
}
