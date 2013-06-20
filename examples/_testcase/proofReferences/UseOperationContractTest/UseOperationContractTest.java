
public class UseOperationContractTest {
	/*@
	  @ ensures \result == 84;
	  @*/
	public int main() {
		int magic = magic42();
		return magic * 2;
	}
	
	/*@
	  @ ensures \result == 42;
	  @*/
	public int magic42() {
		throw new RuntimeException();
	}
}
