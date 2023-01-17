
public class ExistingContractTest {
	/*@ 
	  @ ensures \result == value * 2;
	  @*/
	public int doubleValue(int value) {
		int first = value;
		int second = value;
		return first + second;
	}
}
