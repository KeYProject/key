public class DependencyContractExample {

    private int b;
    private int c;

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == b;
      @ accessible this.b;
      @ assignable \nothing;
      @*/
    public int getB() {
	return b;
    }



    /*@ public normal_behavior
      @ requires n>=0;
      @ ensures c == \old(c) + n && getB() == \old(getB());
      @*/
    public void incC(int n) {
	int y = n;
	/*@ loop_invariant n>=0 && c + n == \old(c) + y && getB() == \old(getB());
	  @ decreases n;
	  @ assignable c;
	  @*/
	while (n > 0) {
	    c++;	
	    n--;
	}
    }


}
