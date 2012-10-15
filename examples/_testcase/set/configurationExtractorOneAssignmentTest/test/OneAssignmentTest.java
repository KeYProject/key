
public class OneAssignmentTest {
	private int value;

	private OneAssignmentTest y;

	private OneAssignmentTest first;

	private OneAssignmentTest second;

	/*@ requires x != null;
	  @ ensures true;
	  @*/
	public int compute(/*@ nullable @*/ OneAssignmentTest x) {
		OneAssignmentTest tempX = x;
		OneAssignmentTest tempY = first;
		first = x;
		second = y;
		return first.value + second.value + tempX.value + tempY.value;
	}
}
