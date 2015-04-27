package recursion;

public class E {
	
	static int i = 0;
	
    //@ public normal_behavior requires i>=0 && i<=2; ensures true;
    public static void e() {
        if (i>=0) A.a();
        i--;
    }
}
