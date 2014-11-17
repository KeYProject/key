

public class BlockContractExample {
    /*@ normal_behavior
      @ ensures \result == 42;
      @*/
	public static /*@ strictly_pure @*/ int main() {
		int x = 0;
		/*@ requires true;
		  @ ensures x == 42;
		  @ assignable x;
		  @ @also
		  @ requires x == 0;
		  @ ensures x == 42;
		  @ assignable x;
		  @*/
		{
			x = 42;
		}
		return x;
	}
}
