package methodCall;

public class MethodCall {
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(Class callme){
		callme.a();
	}
}
