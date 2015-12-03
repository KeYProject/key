final /*@ pure @*/ class Matrix {

    // recursive case for matrices of size > 2
    //@ nullable
    final Matrix a,b,
                 c,d;
    // base case for 2x2 matrix
    final int v11, v12,
	      v21, v22;

    /*@ invariant a==null <==> b==null;
      @ invariant a==null <==> c==null;
      @ invariant a==null <==> d==null;
      @*/

    // create 2x2 matrix
    Matrix (int a, int b,
            int c, int d) {
        this.v11=a; this.v12=b; 
        this.v21=c; this.v22=d;
    }

    // create general matrix
    Matrix (Matrix a, Matrix b,
	    Matrix c, Matrix d) {
        this.a =a; this.b =b;
	this.c =c; this.d =d;
    }

    //@ strictly_pure
    //@ measured_by size();
    public boolean equals(Matrix o) {
	 if (size()==2) {
	     if (o.size()==2) {
                 return (  v11==o.v11 && v12==o.v12
                        && v21==o.v21 && v22==o.v22);
	     } else return false;
	 } else {
             if (o.size()==2)
		 return false;
	     else {
		 return ( a.equals(o.a) && b.equals(o.b)
		       && c.equals(o.c) && d.equals(o.d));
             }
	 }
    }

    //@ strictly_pure
    int size () {
        if (a==null) return 2;
	else return a.size()*2;
    }

    /** matrix addition */
    //@ requires m.size() == n.size();
    //@ measured_by m.size();
    static Matrix plus (Matrix m, Matrix n) {
	if (m.size()==2) {
	    return new Matrix(m.v11+n.v11, m.v12+n.v12,
			      m.v21+n.v21, m.v22+n.v22);
	} else {
	    return new Matrix(plus(m.a,n.a), plus(m.b,n.b),
			      plus(m.c,n.c), plus(m.d,n.d));
	}
    }

    /** matrix negation */
    //@ measured_by m.size();
    static Matrix neg (Matrix m) {
	if (m.size()==2) {
            return new Matrix(-m.v11, -m.v12,
			      -m.v21, -m.v22);
	} else {
	    return new Matrix(neg(m.a), neg(m.b),
			      neg(m.c), neg(m.d));
	}
    }

    /** naive O(n^3) matrix multiplication */
    //@ strictly_pure 
    //@ requires m.size() == n.size();
    //@ measured_by m.size();
    static Matrix mult (Matrix m, Matrix n) {
	if (m.size()==2) {
            return new Matrix(
                m.v11*n.v11 + m.v12*n.v21,  m.v11*n.v12 + m.v12*n.v12,
                m.v21*n.v11 + m.v22*n.v21,  m.v21*n.v12 + m.v22*n.v22);
	} else {
	    return new Matrix(
	        plus(mult(m.a,n.a),mult(m.b,n.c)), 
		plus(mult(m.a,n.b),mult(m.b,n.d)),
		plus(mult(m.c,n.a),mult(m.d,n.c)),
	        plus(mult(m.c,n.b),mult(m.d,n.d)));
	}
    }

    /** fancy O(n^{log 7}) matrix multiplication by Strassen 
    /*@ normal_behavior
      @ requires m.size() == n.size();
      @ ensures \result.equals(mult(m,n));
      @ measured_by size();
    static Matrix strassen (Matrix m, Matrix n) {
        int m1 = (m.a+m.d)*(n.a+n.d);
        int m2 = (m.c+m.d)*n.a;
        int m3 = m.a*(n.b-n.d);
        int m4 = m.d*(n.c-n.a);
        int m5 = (m.a+m.b)*n.d;
        int m6 = (m.c-m.a)*(n.a+n.b);
        int m7 = (m.b-m.d)*(n.c+n.d);
        return new Matrix(
            m1+m4-m5+m7,  m3+m5,
            m2+m4      ,  m1-m2+m3+m6);
    }
    */

}
