
public class MethodBodyExpand {
	/*@
	  @ ensures \result == 42;
	  @*/
	public int main() {
		int result = magic42();
		return result;
	}
	
	public int magic42() {
		return 42;
	}
}
