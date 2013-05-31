// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package pack.pack1;
public class MyClass extends SupClass {

    /*@ invariant b>0; @*/

    private int b;

    static MyClass s;

    private int[] arr;

    static int si;

    MyClass a;

    /*@ ensures b==1; @*/
    MyClass[] c;

    public MyClass myQuery(int i, MyClass m) {
        return m;
    }

    public MyClass myQuery0() {
        int i=0;
        myQuery0();
        return null;
    }

    public MyClass myQ() {
        myQuery0();
        return null;
    }

    public static MyClass myStaticQuery() {
        return null;
    }

    public void rec(int j, int k, int l) {
        int i=0;
        j=i;
        rec(j,j,j);
    }

    /*@ assignable b; ensures \result==null && \old(arr) == arr && \old(arr[1]) == arr[1] ; @*/
    public MyClass m(int i, int j, int k) {
        return null;
    }

    public int i(int i, int j) {
//      a.t();
//      s.t();
//      t();
//      this.t();
//      a.m(i,j,2);
//      s.m(i,j,1);
//      this.m(i,j,0);
//      j();
//      this.j();
//      super.k();
        return i;
    }

    public void t(int i) {

    }

    public abstract int l();

}

class SupClass {
    public int k() {

    }

    public int j() {
        return 3;
    }

}

class SubClass extends MyClass {
    public int l() {
        super.j();
        return 1;
    }

    public int j() {
        return 2;
    }


    public MyClass myQuery(int i, MyClass m) {
        return m;
    }

}

class SubClass1 extends SubClass {
    public int l() {
        super.j();
        return 2;
    }

    public int k() {
        return 3;
    }
}
