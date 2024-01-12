public class BranchingLoop {

	/*@ public normal_behavior
	  @ ensures true;
	  @ diverges true;
	  @ */
	public void doIt(int n){
		int i=0;
		int oldN = n;
		//@ loop_invariant (i+4) / (1+n-oldN) ==  4; modifies i,n;
		while(i < n*2){
			n+=2;
			if(i >= 64){
				foo(n); //NOP
			}
			i+=8;
		}
	}
	
	public void foo(int n){
		//dummy
	}
}
