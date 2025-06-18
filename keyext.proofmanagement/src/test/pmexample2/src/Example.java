import java.util.ArrayList;

class Example {
	/*@ ensures param != 7 && param >= 0 ==> \result == 42;
	  @ diverges param == 7 || param < 1;
	  @*/
	int root(final int param) {
		new java.util.ArrayList();
		return left(param) + right();
	}
	
	/*@
	  @ ensures \result == 21;
	  @*/
	int right() {
		return recursive(42);
	}
	
	/*@ ensures \result == 21;
	  @ measured_by i;
	  @*/
	int recursive(final int i) {
		if (i <= 0)
			return result();
		else
			return recursive(i-1);
	}
	
	/*@
	  @ ensures \result == 21;
	  @*/
	int result() {
		return 21;
	}
	
	/*@ ensures param != 7 && param >= 0 ==> \result == 21;
	  @ diverges param == 7 || param < 0;
	  @*/
	int left(final int param) {
		if (param == 7)
			block();
		else
			return cycleA(param);
	}
	
	/*@
	  @ diverges true;
	  @*/
	void block() {
		block();
	}
	
	/*@ ensures param >= 0 ==> \result == 21;
	  @ measured_by param;
	  @ diverges param < 0;
	  @*/
	int cycleA(final int param) {
		if (param == 0 || param == 1)
			return leaf();
		else
			return cycleB(param-1);
	}
	
	/*@ ensures param > 0 ==> \result == 21;
	  @ measured_by param;
	  @ diverges param <= 0;
	  @*/
	int cycleB(final int param) {
		return cycleA(param-1);
	}
	
	/*@
	  @ ensures \result == 21;
	  @*/
	int leaf() {
		return 21;
	}
}
