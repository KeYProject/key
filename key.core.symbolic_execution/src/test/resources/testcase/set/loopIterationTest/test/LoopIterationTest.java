
public class LoopIterationTest {
	public void loopMultipleTimes() {
		doLoop();
		doLoop();
	}
	
	public void doLoop() {
		int i = 0;
		while(i < 3) {
			i += innerLoop();
		}
	}
	
	public int innerLoop() {
		return 1;
	}
	
	public void main() {
		int i = 0;
		while(i < 3) {
			i++;
		}
	}
	
	public void mainWorks() {
		int i = 0;
		while (i < 3) {
			i++;
		}
		int j;
	}
}
