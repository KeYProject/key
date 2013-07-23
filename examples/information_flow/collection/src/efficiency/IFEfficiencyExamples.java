/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package efficiency;


/**
 *
 * @author christoph
 */
public class IFEfficiencyExamples {
    private int h;
    public int l;

    //@ separates l;
    void mWithBlockContract() {
        // fix l value
        //@ normal_behavior separates l;
        { if (l < 0) { l = 0;} }
        //@ normal_behavior separates l;
        { if (l > 8) { l = 8; } }

        // fix h value
        //@ normal_behavior separates l;
        { if (h < 0) { h = 0; } }
        //@ normal_behavior separates l;
        { if (h > 8) { h = 8; } }

        // calculate h result
        //@ normal_behavior separates l;
        { h = h * l; }
    }

    //@ separates l;
    void mWithoutBlockContract() {
        // fix l value
        if (l < 0) { l = 0; }
        if (l > 8) { l = 8; }

        // fix h value
        if (h < 0) { h = 0; }
        if (h > 8) { h = 8; }

        // calculate h result
        h = h * l;
    }

}
