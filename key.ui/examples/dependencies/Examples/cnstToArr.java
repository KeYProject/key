package de.uka.ilkd.key.loopinvgen.Examples;

public class cnstToArr {
	int a[];

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
			a[i] = 1;
			// i++;
		}

	}
}
