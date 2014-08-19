package us;

import op.OP;

public class US {
	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public US() {
	}
	
	public int unspecified() {
		return 42;
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
