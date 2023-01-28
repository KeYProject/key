package methodCallWithAssignmentWithinClass;

public class MethodCallWithAssignmentWithinClass {
	
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(){
		boolean nottrue = callme();
	}
	
	
	public boolean callme(){
		return false;
	}
}
