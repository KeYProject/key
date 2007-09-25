public class FailedStaticInit {

    public static int ATTR;
 
    static {
	A.SAVE = new FailedStaticInit();
	int a = 0 / (3-3);
    }

    public int objectVar = 0;

    public FailedStaticInit() {
    }

    public void objectMethod() {
	this.objectVar = 3;
        FailedStaticInit.ATTR = 0;
    }

}
