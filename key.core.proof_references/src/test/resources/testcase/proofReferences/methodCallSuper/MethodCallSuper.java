package methodCallSuper;

public class MethodCallSuper extends Super{
	/*@requires true;
	  @ensures true;
	  @*/
	public void caller(){
		super.a();
	}
}