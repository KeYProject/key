package de.uka.ilkd.key.loopinvgen.Examples;
/* a is a FieldReference -> Covered
 * i is a LocationVariable -> TODO
 */
public class varToVar{
	int a;
	int b;
	/*@ public normal_behavior
	  @ requires true;
	  @ ensures true;
	  @*/
	public void func(int n) {
		int i = 0;
		/*@ loop_invariant
		 @ i>=0 && i<n && \dl_noR(\singleton(this.a)) && \dl_noRaW(\singleton(this.a)) && \dl_noWaR(\singleton(this.a)) && \dl_noWaW(\singleton(this.a));
		 @ decreases n-i;
		 @ assignable a;
		 @*/
		while(i < n) {
			a = b;
			//i++;
		}
	}
	
}