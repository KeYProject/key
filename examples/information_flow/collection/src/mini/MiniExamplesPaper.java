package mini;

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author christoph
 */
public class MiniExamplesPaper {
    public static int l;
    private static int h;


    // From "Abstract Interpretation of Symbolic Execution with Explicit State Updates"

    /*@ normal_behavior
      @     respects    l;
      @*/
    void insecure_p1_1() {
        l = h;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void insecure_p1_2() {
        if (h>0) {l=1;} else {l=2;};
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    /*@ normal_behavior
      @     respects    l;
      @     diverges true;
      @*/
    void secure_p1_1() {
        if (l>0) {h=1;} else {h=2;};
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p1_2() {
        if (h>0) {l=1;} else {l=2;}; l=3;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p1_3() {
        h=0; l=h;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p1_4() {
        if (h>0) {h=l; l=h;};
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p1_5() {
        if (h>0) {l=2; h=1;} else {l=2; h=2;};
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p1_6() {
        l = h-h;
    }


    // From "A Theorem Proving Approach to Analysis of Secure Information Flow"

    /*@ normal_behavior
      @     respects    l;
      @*/
    void insecure_p2_1() {
        l = h;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_1() {
        h = l;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_2() {
        l = 6;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_3() {
        l=h; l=6;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_4() {
        h=l; l=h;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_5() {
        l=h; l=l-h;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_6() {
        if (false) l=h;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void insecure_p2_2() {
        if (h>=0) l=1; else l=0;
    }

    /*@ normal_behavior
      @     respects    l;
      @*/
    void secure_p2_7() {
        if (h==1) l=1; else l=0; l=0;
    }

}
