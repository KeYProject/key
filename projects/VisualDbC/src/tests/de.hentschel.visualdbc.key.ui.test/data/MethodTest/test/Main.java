
public class Main {
	/*@
	  @ ensures \result == 84;
	  @*/
	public int main() {
		int first = Util.getMagic();
		int second = Util.getMagic();
		return Util.add(first, second);
	}
	
   /*@
     @ ensures true;
     @*/
	public void unusedMethod() {
	}
}
