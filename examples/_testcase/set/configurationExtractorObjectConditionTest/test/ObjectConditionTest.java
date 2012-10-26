
public class ObjectConditionTest {
	private int x;
	
	private ObjectConditionTest next;
	
	public static ObjectConditionTest instance;
	
	public int compute(int a) {
		if (x == 1) {
			if (next.x == 2) {
				if (next.next.x == 3) {
					if (instance.x == 4) {
						if (instance.next.x == 5) {
							if (instance.next.next.x == 6) {
								return 42;
							}
							else {
								return -600;
							}
						}
						else {
							return -500;
						}
					}
					else {
						return -400;
					}
				}
				else {
					return -300;
				}
			}
			else {
				return -200;
			}
		}
		else {
			return -100;
		}
	}
}
