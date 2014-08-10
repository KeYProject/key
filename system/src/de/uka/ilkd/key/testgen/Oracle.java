package de.uka.ilkd.key.testgen;

public class Oracle {
	
	private String preCall;
	private String postCall;
	public Oracle(String preCall, String postCall) {
	    super();
	    this.preCall = preCall;
	    this.postCall = postCall;
    }
	public String getPreCall() {
		return preCall;
	}
	public String getPostCall() {
		return postCall;
	}
	
	
	

	
}
