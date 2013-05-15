package methodCallWithAssignment;

public class MethodCall {
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(Class callme){
		boolean fu = callme.a();
	}
}
