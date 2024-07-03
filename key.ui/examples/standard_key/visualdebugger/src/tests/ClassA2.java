package tests;

public class ClassA2 {

	private/* @ spec_public @ */int i;

	public/* @pure@ */ClassA2() {
		i = 20;
	}

	public int myFunction() {

		return i;
	}

}
