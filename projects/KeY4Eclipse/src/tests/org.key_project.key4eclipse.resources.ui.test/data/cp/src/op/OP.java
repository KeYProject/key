package op;

public class OP {
	/*@ normal_behavior
	  @ ensures true;
	  @*/
	public OP() {
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
		return wrong();
	}
	
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public static int wrong() {
		return 66;
	}
}
