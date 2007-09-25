public class Inv {
    /*@ public normal_behavior
      @requires n >= 0;
      @ensures \result==n;
      @
     @*/
    public static int test(int n) {
	int i = 0;
	/*@
	  @ loop_invariant 0<= i && i<=n;
	  @ assignable i;
	  @ decreases n-i;
	  @ */
	while (i < n) {
	    i++;
	    while (true) ;
	    
	}
	return i;
    }

    public static void main(String args[]) {
	System.out.println(test(4));
    }
}