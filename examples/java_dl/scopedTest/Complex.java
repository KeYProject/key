import javax.realtime.*;

public class Complex{

    int real = 0;
    int im = 0;

    public static /*@nullable@*/ Complex zero;

    private /*@nullable@*/ Complex conjugate;

    public Complex(int real, int im){
	this.real = real;
	this.im = im;
    }

    /*@ public normal_behavior
      @  requires \outerScope(\currentMemoryArea, \memoryArea(this));
      @  working_space conjugate==null ? \space(Complex) : 0;
      @*/
    public Complex getConjugate(){
	if(conjugate==null){
	    conjugate=new Complex(real, -im);
	}
	return conjugate;
    }

    public Complex /*@scopeSafe@*/ getConjugateScopeSafe(){
	return new Complex(real, -im);
    }

    public Complex /*@scopeSafe@*/ add(Complex a){
	return new Complex(a.real+real, a.im+im);
    }

    /*@ public normal_behavior
      @  requires zero==null ==> \currentMemoryArea==ImmortalMemory.instance();
      @  assignable zero, \object_creation(Complex);
      @  working_space zero==null ? \space(Complex) : 0;
      @  ensures \inImmortalMemory(\result);
      @*/
    public static Complex zero(){
	if(zero==null){
	    zero=new Complex(0, 0);
	}
	return zero;
    }

}
