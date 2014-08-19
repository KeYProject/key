package cl;

public class CP {
	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public CP() {
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int correct() {
		return 42;
	}
}
