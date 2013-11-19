/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package object;


/**
 *
 * @author christoph
 */
public class AmtoftBanerjee3 {
    int x, a, b;

    //@ requires (a % 4) == 3;
    //@ separates \nothing \declassifies x \erases b;
    void m() {
        b = x + (a % 4);
    }
}
