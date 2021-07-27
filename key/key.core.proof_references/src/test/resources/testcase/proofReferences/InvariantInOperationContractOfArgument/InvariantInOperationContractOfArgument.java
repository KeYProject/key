
public class InvariantInOperationContractOfArgument {
	private static int y;
	
	/*@ requires \invariant_for(child);
	  @ ensures child.x == newValue;
	  @ ensures \invariant_for(child);
	  @ assignable \everything;
	  @*/
	public static void main(Child child, int newValue) {
		child.x = newValue;
	}
}
