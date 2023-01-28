
public class LabelTest {
	public static int lost() {
		int i = 3;
		labeledBlock: {
			i++;
		    labeledStatement: i = i + 1;
			i--;
		}
		return i;
	}
	
	public static int doubled() {
		labeledBlock: {
		   int i = 0;
		   i++;
		   return i;
    	}
	}
}
