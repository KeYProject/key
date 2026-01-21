package methodCallWithAssignmentSuper;

public class MethodCallWithAssignmentSuper extends Super{
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(){
		boolean fu = super.a();
	}
}
