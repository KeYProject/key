
public class UseOperationContractExceptionalNoPreconditionWithNullCheckTest {
	public static int main(UseOperationContractExceptionalNoPreconditionWithNullCheckTest obj) {
		try {
			int magicNumber = obj.magic(123);
			int magicNumberCopy = magicNumber;
			return magicNumber + magicNumberCopy;
		}
		catch (Exception e) {
			return -1;
		}
	}
	
	/*@ public exceptional_behavior
	  @ signals (Exception myExc) true;
	  @*/
	public int magic(int x) throws Exception {
		return 42;
	}
}
