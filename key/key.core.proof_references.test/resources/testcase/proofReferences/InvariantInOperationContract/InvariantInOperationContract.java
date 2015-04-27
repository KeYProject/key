
public class InvariantInOperationContract {
	private Child child;
	
	private int y;
	
	/*@ requires \invariant_for(child);
	  @ ensures y == newValue;
	  @*/
	public void main(int newValue) {
		y = newValue;
	}
}
