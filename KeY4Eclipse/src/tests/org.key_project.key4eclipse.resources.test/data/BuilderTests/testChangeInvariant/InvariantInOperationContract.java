
public class InvariantInOperationContract {
	
	/*@ requires \invariant_for(child);
	  @ ensures child.x == newValue;
	  @ ensures \invariant_for(child);
	  @ assignable \everything;
	  @*/
	public static void main(Child child, int newValue) {
		child.x = newValue;
	}
	

	//@ ensures \result == x + y;
	public int add(int x, int y){
		return x + y;
	}
}
