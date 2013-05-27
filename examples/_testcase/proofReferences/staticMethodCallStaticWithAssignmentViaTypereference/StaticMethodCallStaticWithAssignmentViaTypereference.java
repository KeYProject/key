package staticMethodCallStaticWithAssignmentViaTypereference;

public class StaticMethodCallStaticWithAssignmentViaTypereference {
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(){
		boolean nottrue = StaticClass.callMe();
	}
}
