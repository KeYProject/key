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
    void xZero() {
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
    void disjoint() {
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
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
     */
    void disjoint2() {
        disjointHelper2();
    }


    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        assignable  rep1, rep2, rep3, rep4, rep5;
     */
    void disjointHelper2() {
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
    void disjoint3() {
        disjointHelper3();
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
    void disjointHelper3() {
    }
}
