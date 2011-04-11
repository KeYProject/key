public class Query {


    /*@ public normal_behavior 
      @ requires true;
      @ ensures \result == 0;
      @*/
    public /*@ pure @*/ int query() {
	return 0;
    }

    /*@ public normal_behavior 
      @ requires a>0;
      @ ensures \result > 0;
      @*/
    public /*@ pure @*/ int query(int a) {
	return a;
    }

    /*@ public normal_behavior 
      @ requires a>0;
      @ ensures \result > 0;
      @*/
    public static /*@ pure @*/ int query(int a, int b) {
	return a+b;
    }


    /*@ public normal_behavior 
      @ requires true;
      @ ensures \result == query(2) + query(1,2) + query();
      @*/
    public /*@ pure @*/ int m() {
	return 5;
    }


}