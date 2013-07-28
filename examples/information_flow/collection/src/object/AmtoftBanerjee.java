/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package object;


/**
 *
 * @author christoph
 */
public class AmtoftBanerjee {

    int q;

    //@ normal_behavior
    //@ assignable \nothing;
    //@ separates \nothing \declassifies q \erases \result;
    int getQ() {
        return this.q;
    }

    //@ normal_behavior
    //@ assignable q;
    //@ separates \nothing \declassifies n \erases q;
    void setQ(int n) {
        this.q = n;
    }


    static int secret, z;

    //@ normal_behavior
    //@ separates \nothing \declassifies secret \erases z;
    //@ also
    // the following contract is not satisfied
    //@ normal_behavior
    //@ separates \nothing \erases z;
    static void m_1() {
        AmtoftBanerjee x1;
        AmtoftBanerjee x2 = new AmtoftBanerjee();
        x1 = x2;
        x1.setQ(secret);
        z = x2.getQ();
    }

    //@ normal_behavior
    //@ separates \nothing \erases z;
    static void m_2() {
        AmtoftBanerjee x1 = new AmtoftBanerjee();
        AmtoftBanerjee x2 = new AmtoftBanerjee();
        x1.setQ(secret);
        z = x2.getQ();
    }
}
