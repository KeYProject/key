
public class ElseIfTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int elseIf(int x) {
		int a;
		if (x == 0) {
			a = 1;
		}
		else if (x == 1 || x == 2 || x == 3) {
			if (x == 1 || x == 2) {
				a = -1;
			}
			a = x * x;
		}
		else if (x == 4) {
			return 42;
		}
		else {
			a = x;
		}
		return a;
	}
}
