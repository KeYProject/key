package newSubType.changed;

public class Main {
	/*@
	  @ensures \result == 42;
	  @*/
	public int main(A a) {
		return a.getValue();
	}
}