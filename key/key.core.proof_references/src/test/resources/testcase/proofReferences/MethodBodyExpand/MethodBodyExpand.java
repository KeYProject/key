
public class MethodBodyExpand {
	/*@
	  @ ensures \result == 84;
	  @*/
	public int main() {
		int first = magic42();
      int second = magic42();
		return first + second;
	}
	
	public int magic42() {
		return 42;
	}
}
