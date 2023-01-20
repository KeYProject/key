
public class EmptyBlockTest {
	public static int emptyBlocks() {
		if (true) {
		}
		label1: break label1;
		label2: {
		   break label2;
	    }
		label3: {
	    }
	    label4 : ;
	    ;
	    {
	    }
	    ;;;;;
	    {{{}}{}}{}
	    return 0;
	}
}