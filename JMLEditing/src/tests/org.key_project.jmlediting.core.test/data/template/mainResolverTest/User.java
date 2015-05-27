package main.core.account;

public class User {

	private String name = "";
	private static int userCount = 0;
	
	public User(String name) {
	    userCount++;
		this.name = name;
	}
	
	public static int getUserCount() {
	    return userCount;
	}
	
	public /*@ pure @*/ String getName() {
		return name;
	}

	/*@ normal_behavior
	  @ ensures this.name = name;
	  @*/
	public void setName(String name) {
		this.name = name;
	}

	
	
	
}
