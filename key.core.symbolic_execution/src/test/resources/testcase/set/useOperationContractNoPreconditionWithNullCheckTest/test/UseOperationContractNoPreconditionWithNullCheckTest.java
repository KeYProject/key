
public class UseOperationContractNoPreconditionWithNullCheckTest {
	public static int main(UseOperationContractNoPreconditionWithNullCheckTest obj) {
		int magicNumber = obj.magic(123);
		int magicNumberCopy = magicNumber;
		return magicNumber + magicNumberCopy;
	}
	
	/*@ public normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int magic(int x) {
		return 42;
	}
}
