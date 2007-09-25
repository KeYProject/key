// geht nich:  ensures \result == ((n > 100) ? (n - 10) : 91);

public class Function91 {
    /*@ public normal_behavior
      @ requires true;
      @ ensures ( (n > 100) ==> \result == n - 10 ) &&
                ( (n <= 100) ==> \result == 91 );
      @ assignable \nothing;
      @ diverges true;
      @*/
    public static int f ( int n ) {
	if (n > 100) return n - 10;
	else return f(f(n+11));
    }
}
