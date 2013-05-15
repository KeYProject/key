package variableDeclarationAssign;

public class VariableDeclarationAssign {
	boolean a;
	
	/*@ requires true;
	  @ ensures true;
	  @*/
	public void caller() {
		boolean fu = a;
	}
}
