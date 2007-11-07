package prettyprinter;

public class Pretty {

	public static void main(String[] args) {
		
		demo(5);

	}

	/*@public normal_behavior requires true; ensures true;@*/
	public static int demo(int i) {
		if (i < 50) {
			if (i < 30) {
				return 30;
			} else {
				if (i < 20) {
					return 20;
				} else {
					if (i < 10)
						return 10;

				}
			}
		}
		if (i > 50) {
			if (i > 60) {
				return 60;
			} else {
				if (i > 70) {
					return 70;
				} else {
					if (i > 80)
						return 80;

				}
			}
		}
		return i;
	}

}
