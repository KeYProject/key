
public class ContractTest {
	/*@
	  @ requires value == 2;
	  @ also
	  @ requires value == 4;
	  @*/
	public int returnValue(int value) {
		return value;
	}
}
