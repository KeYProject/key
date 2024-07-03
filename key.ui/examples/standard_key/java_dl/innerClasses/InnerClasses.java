/**
 * This class can be used to test the inner classes mechanism
 */

class InnerClasses {

    private int privField = 0;
    
    class Innerst {

	Innerst(int val) {
	    // ignore argument
	}
	
	void setPrivField() {
	    privField = 1;
	}
    }


    void anonClass() {
	final int newValue = 2;

	Innerst anon = new Innerst(17) {
		void setPrivField() {
		    privField = newValue;
		}
	    };

	anon.setPrivField();
    }

/*  
    // for comparison only
    public static void main(String args[]) {
	InnerClasses ic = new InnerClasses();
	InnerClasses.Innerst i = ic.new Innerst(42);
	
	System.out.println("pre: " + ic.privField);

	i.setPrivField();
	System.out.println("post 1: " + ic.privField);

	ic.anonClass();
	System.out.println("post 2: " + ic.privField);
    }
*/

}
