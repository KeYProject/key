
public class NestedInvariantInOperationContract {
	private ChildContainer cc;
	
	private int y;
	
	/*@ requires cc != null && \invariant_for(cc.child);
	  @ ensures y == newValue;
	  @*/
	public void main(int newValue) {
		y = newValue;
	}
}
