public class Number {
	private int content;

	/*@ normal_behavior
	  @ requires true;
	  @ ensures true;
	  @*/
	public boolean equals(Object n) {
	   if (n instanceof Number) {
	      if (content == ((Number) n).content) {
	         return true;
	      }
	      else {
	         return false;
	      }
	   }
	   else {
	      return false;
	   }
	}
}