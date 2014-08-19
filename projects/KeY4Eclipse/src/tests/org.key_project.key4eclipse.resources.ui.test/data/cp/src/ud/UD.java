package ud;

import op.OP;

public class UD {
	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public UD() {
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int correct() {
		return 42;
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int correctUnprovenDependency() {
		return OP.wrong();
	}
}
