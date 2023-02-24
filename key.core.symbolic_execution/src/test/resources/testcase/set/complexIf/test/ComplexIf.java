
public class ComplexIf {
	/* Start
	 * self.min(_i_i, _j_j)
	 * int result;
	 * if (i < j && i != j)
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
		if (i < j && i != j) {
			result = i;
		}
		else {
			result = j;
		}
		return result;
	}
}
