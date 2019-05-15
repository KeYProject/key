
public class SwitchCaseTest {
	public int switchCase(int x) {
		int a;
		switch (x) {
		   case 0 : a = 1;
		            break;
		   case 1 :
		   case 2 : a = -1;
		   case 3 : a = x * x;
                    break;
		   case 4 : return 42;
		   default : a = x;
		}
		return a;
	}
}
