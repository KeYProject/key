public class Person {
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
