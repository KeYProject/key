
/* This class is declared final to allow inlining of the method body.
 * If it were not declareed final there might be a subclass of Person
 * with a different implementation.
 */

public final class Person {
    private int age = 0;

    public void setAge(int newAge) {
	this.age = newAge;
    }

    public void birthday() {
	if (age >= 0) {
	    age++;
	} 
    }
}
