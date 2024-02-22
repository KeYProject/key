class Div {
	/*@ public normal_behavior
	  @ diverges i >= 0;
	  @ ensures \result == 0;
	  @*/
	public int m(int i) {
		while (i >= 0) i--;
		return i;
	}
}
