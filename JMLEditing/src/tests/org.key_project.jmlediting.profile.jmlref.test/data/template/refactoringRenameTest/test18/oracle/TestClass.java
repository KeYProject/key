package test;

public class TestClass<IJavaProject> {
    public int newName;
    IJavaProject project;
    
    /*@ normal_behavior
      @ ensures Integer.toString(newName).equals("5") ==> \result == 0;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        if (Integer.toString(newName).equals("5"))
            return 0;
        else
        	return 1;
    }
    
    /*@ normal_behavior
      @ ensures \result == project.getClass().getDeclaredField("balance").equals(newName);
      @*/
    public boolean doSomething() throws NoSuchFieldException, SecurityException{
    	
    	return (project.getClass().getDeclaredField("balance").equals(newName));
    }
}
