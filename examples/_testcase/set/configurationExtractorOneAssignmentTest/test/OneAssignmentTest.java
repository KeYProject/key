
public class OneAssignmentTest {
	private OneAssignmentTestValueWrapper y;

	private OneAssignmentTestValueWrapper first;

	private OneAssignmentTestValueWrapper second;

	/*@ requires x != null;
	  @ ensures true;
	  @*/
	public int compute(/*@ nullable @*/ OneAssignmentTestValueWrapper x) {
		OneAssignmentTestValueWrapper tempX = x;
		OneAssignmentTestValueWrapper tempY = y;
		first = x;
		second = y;
		return first.value + second.value + tempX.value + tempY.value;
	}
}

class OneAssignmentTestValueWrapper {
	public int value;
}
