package de.uka.ilkd.key.testgen;

public class Assignment {
	private final String type;
	private final String left;
	private final String right;

	public Assignment(String left, String right) {
		super();
		type = "";
		this.left = left;
		this.right = right;
	}

	public Assignment(String type, String left, String right) {
		super();
		this.type = type;
		this.left = left;
		this.right = right;
	}

	@Override
	public String toString() {
		return "\n   " + type + " " + left + " = " + right + ";";
	}
}
