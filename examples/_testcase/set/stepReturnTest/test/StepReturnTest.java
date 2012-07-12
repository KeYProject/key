
public class StepReturnTest {
	public void main(int a) {
		firstLevel(a);
		firstLevel(a);
		a = a * 4;
	}
	
	public void firstLevel(int a) {
		secondLevel(a);
		secondLevel(a);
	}

	public void secondLevel(int a) {
		try {
			thirdLevel(a);
		}
		catch (Exception e) {
			a = a * 2;
		}
	}

	public int thirdLevel(int a) {
		fourthLevel(a);
		int notReachable = 3;
		return notReachable;
	}

	public void fourthLevel(int a) {
		throw new Exception();
	}
}
