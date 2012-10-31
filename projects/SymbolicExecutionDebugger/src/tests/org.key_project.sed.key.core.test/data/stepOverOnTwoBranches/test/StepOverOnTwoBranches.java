
public class StepOverOnTwoBranches {
	public int main(int a) {
		if (a == 0) {
			int i = 2;
			int j = 3;
			int x = valueLonger(i);
			int y = value(j);
			int z = valueLonger(x) + valueLonger(y);
			int zz = value(-3) + 
					 value(-4);
			return value(z + zz);
		}
		else {
			int i = 2;
			int j = 3;
			int x = value(i);
			int y = valueLonger(j);
			int z = value(x) + value(y);
			int zz = valueLonger(-3) + 
					valueLonger(-4);
			return valueLonger(z + zz);
		}
	}
	
	public int value(int i) {
		return i;
	}

	
	public int valueLonger(int i) {
		int j = i;
		i = j;
		return j;
	}
}
