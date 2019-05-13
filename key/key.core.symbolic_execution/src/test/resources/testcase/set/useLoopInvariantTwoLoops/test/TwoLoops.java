
public class TwoLoops {
	public static int main(int x) {
		if (x >= 0) {
			/*@ loop_invariant x >= 0;
			  @ decreasing x;
			  @ assignable \strictly_nothing;
			  @*/
			while (x > 0) {
				x--;
			}
		}
		else {
			//@ ghost int originalX = x;
			/*@ loop_invariant x <= 0;
			  @ decreasing originalX - x;
			  @ assignable \strictly_nothing;
			  @*/
			while (x < 0) {
				x++;
			}
		}
		return x;
	}
}
