/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package aliasing;

/**
 *
 * @author christoph
 */
public class AliasingExamples {
    int x;
    
    /*@ requires a != b;
      @ respects \result, b.x;
      @*/
    int secure_1(AliasingExamples a, AliasingExamples b, int h) {
        a.x = h;
        return b.x;
    }
    
    /*@ respects \result, b.x;
      @*/
    int insecure_1(AliasingExamples a, AliasingExamples b, int h) {
        a.x = h;
        return b.x;
    }
}
