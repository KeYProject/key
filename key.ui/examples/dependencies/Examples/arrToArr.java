package de.uka.ilkd.key.loopinvgen.Examples;

public class arrToArr {
	int a[], b[];

	/*@
	 @ public normal_behavior
     @ requires true;
	 @ ensures true;
	 @*/
	
	public void func(int n) {
		int i = 0;
		/*@ loop_invariant
		 @ i>=0 && i<n;
		 @ decreases n-i;
		 @ assignable a[0..n];
		 @*/
		while (i < n) {
			a[i] = b[i];
			// i++;
		}

	}
}
