
public class FunctionalIf {
	/* Start
	 * self.min(_i_i, _j_j)
	 * int result;
	 * if (confert(i) < convert(j))
	 * self.invert(_i_i) @FunctinalIfParameter
	 * return a * -1;
	 * return _i_i * -1 @ return of method invert
	 * self.invert(_j_j) @FunctinalIfParameter
	 * return a * -1;
	 * return _j_j * -1 @ return of method invert
	 *    => BC: _j_j >= 1 + _i_i
	 *       result = i;
	 *       return result;
	 *       return _i_i
	 *       <endNode>
	 *    => BC: _j_j <= _i_i
	 *       result = j;
	 *       return result;
	 *       return _j_j
	 *       <endNode>
	 */
	
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int min(int i, int j) {
		int result;
		if (invert(i) < invert(j)) {
			result = i;
		}
		else {
			result = j;
		}
		return result;
	}
	
	public int invert(int a) {
		return a * -1;
	}
}
