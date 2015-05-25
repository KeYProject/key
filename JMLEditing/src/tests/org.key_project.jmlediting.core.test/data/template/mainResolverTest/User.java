package main.core.account;

public class User {

	private String name = "";
	
	public User(String name) {
		this.name = name;
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
