/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package object;


/**
 *
 * @author christoph
 */
public class AmtoftBanerjee2 {
    int marg, res;
    //@ invariant (marg != 0) ==> (res == expensive(marg));

    //@ normal_behavior
    //@ assignable marg, res;
    //@ separates z, \result;
    int cexp(int z) {
        if (z == marg && z != 0) {
            return res;
        } else {
            int result = expensive(z);
            marg = z;
            res = result;
            return result;
        }
    }

    //@ normal_behavior
    //@ ensures \result == expensive(z);
    //@ assignable \nothing;
    //@ accessible \nothing;
    //@ separates z, \result;
    int expensive(int z) {
        return z;
    }
}
