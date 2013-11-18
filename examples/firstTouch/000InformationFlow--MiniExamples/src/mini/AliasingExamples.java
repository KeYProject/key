/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package mini;

/**
 *
 * @author christoph
 */
public class AliasingExamples {
    int x;
    
    /*@ requires a != b;
      @ separates \result, b.x;
      @*/
    int secure_1(AliasingExamples a, AliasingExamples b, int h) {
        a.x = h;
        return b.x;
    }
    
    /*@ separates \result, b.x;
      @*/
    int insecure_1(AliasingExamples a, AliasingExamples b, int h) {
        a.x = h;
        return b.x;
    }
}
