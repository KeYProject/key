public class Number {
	private int content;

	/*@ normal_behavior
	  @ requires true;
	  @ ensures true;
	  @*/
	boolean equals(@org.jspecify.annotations.Nullable Object n) {
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