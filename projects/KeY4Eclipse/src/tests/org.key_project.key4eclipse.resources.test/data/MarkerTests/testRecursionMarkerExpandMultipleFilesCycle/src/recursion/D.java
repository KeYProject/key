package recursion;

public class D {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void d() {
        if (i>=0) E.e();
        i--;
    }
}
