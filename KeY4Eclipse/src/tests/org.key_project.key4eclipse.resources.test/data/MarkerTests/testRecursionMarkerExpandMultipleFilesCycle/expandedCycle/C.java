package recursion;

public class C {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void c() {
        if (i>=0) D.d();
        i--;
    }
}
