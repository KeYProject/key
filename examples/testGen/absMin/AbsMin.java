public class AbsMin{

    /*@ public normal_behavior
      @   ensures \result == ((a<b? a : b)<0 ? -(a<b? a : b) : (a<b? a : b));
      @*/
    public static int absMin(int a, int b){
	int result = b;
	if(a<b){
	    result = a;
	}
	if(result<0){
	    result = -result;
	}
	return result;
    }

}
