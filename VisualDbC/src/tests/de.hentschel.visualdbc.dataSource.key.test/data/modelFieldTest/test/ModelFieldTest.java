public class ModelFieldTest {
	//@ model int f;
	//@ accessible f : this.x;
	//@ represents f = 2 * x;
	
	private int x = 4;
	
	/*@ normal_behavior
	  @ ensures \result == f;
	  @*/
	public int doubleX() {
		return x + x;
	}
}