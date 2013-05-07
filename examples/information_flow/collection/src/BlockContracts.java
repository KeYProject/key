/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author christoph
 */
public class BlockContracts {
    int x;
    
    //@ ensures x > 4;
    public void m1() {
        l0:
        {
            // @ ensures x > 4;
            l1:
            {
                x = 5;
                break l0;
            }
        }
        x++;
    }
    
    //@ ensures x > 4;
    public void m2() throws Exception {
        throw new Exception();
    }
    
    
    /*@ requires x <= 4;
      @ ensures x > 4;
      @*/
    public void m3() {
        l0: 
        /*@ loop_invariant  x <= 4;
          @ decreases       4 - x;
          @*/
        while (x < 4) {
            x++;    
            continue l0;
        }
        x++;
    }
    
    
}
