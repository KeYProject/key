/**
 *
 * @author christoph
 */
public class Disjoint {
    int x, y;
    //@ ghost \locset rep;
    //@ ghost \locset rep1;
    //@ ghost \locset rep2;
    //@ ghost \locset rep3;
    //@ ghost \locset rep4;
    //@ ghost \locset rep5;
    //@ ghost \locset rep6;
    //@ ghost \locset rep7;
    //@ ghost \locset rep8;
    //@ ghost \locset rep9;
    //@ ghost \locset rep10;
    //@ ghost \locset rep11;
    //@ ghost \locset rep12;


    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_1() {
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_2() {
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_4() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_8() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_10() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
        assignable  y;
     */
    void xZeroHelper(){
    }



    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_1() {
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_2() {
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_4() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_8() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_10() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
        assignable  y, rep;
     */
    void disjointHelper() {
    }


    /*@ requires    \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep1);
     */
    void disjoint2_1() {
        disjointHelper2_1();
    }


    /*@ requires    \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep1);
        assignable  rep1;
     */
    void disjointHelper2_1() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
     */
    void disjoint2_2() {
        disjointHelper2_2();
    }


    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        assignable  rep1, rep2;
     */
    void disjointHelper2_2() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
     */
    void disjoint2_4() {
        disjointHelper2_4();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        assignable  rep1, rep2, rep3, rep4;
     */
    void disjointHelper2_4() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
     */
    void disjoint2_8() {
        disjointHelper2_8();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8;
     */
    void disjointHelper2_8() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        requires    \disjoint(rep, rep10);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep10);
     */
    void disjoint2_10() {
        disjointHelper2_10();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        requires    \disjoint(rep, rep10);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep10);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8, rep9, rep10;
     */
    void disjointHelper2_10() {
    }
}
