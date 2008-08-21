public class Complex{

    int real = 0;
    int im = 0;

    private /*@nullable@*/ Complex conjugate;

    public Complex(int real, int im){
	this.real = real;
	this.im = im;
    }

    public Complex /*@scopeSafe@*/ getConjugate(){
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

}
