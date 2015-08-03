
public class Main {
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @*/
	public int main(B b) {
		return magic(b);
	}

   public int magic(A a) {
      return 42;
   }
   
   public int magic(B b) {
      return 99;
   }
}
