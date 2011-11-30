/** This is an example to illustrate JML's \bigint type,
 * which always represents mathematical integers no matter what
 * Java integer semantics are in force.
 */
public class Mult {

    // Without any pre condition, this post condition is not valid
    // in the checking-overflow semantics.
    // To prove it, we need to assume that the (mathematical) product
    // is within the bounds of Java integers,
    // which means we have to express this property using a different
    // (ignoring-overflow) semantics.

    /*@ public normal_behavior
      @ requires -2147483648 < x;
      @ requires -2147483648 <= (\bigint)x * (\bigint)y;
      @ requires (\bigint)x * (\bigint)y <= 2147483647;
      @ ensures \result == x * y;
      @*/
    public int mult (int x, int y){
        int z = 0;
        boolean p = x > 0;
        if (p) x = -x;
	//@ ghost int oldx = x;
	/*@ maintaining oldx <= x && x <= 0;
          @ maintaining z == y * (p? (\old(x)+x) : (x-\old(x)));
          @ decreasing -x;
	  @*/
        while (x++ < 0) z += y;
        return p? z: -z;
    }
}
