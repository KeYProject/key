package staticMethodCallStaticViaTypereference;

public class StaticMethodCallStaticViaTypereference {
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(){
		StaticClass.callMe();
	}
}
