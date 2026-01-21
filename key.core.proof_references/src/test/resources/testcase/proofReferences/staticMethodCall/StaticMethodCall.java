package staticMethodCall;

public class StaticMethodCall {
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(StaticClass staticClass){
		staticClass.callMe();
	}
}
