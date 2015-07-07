package test;

import TestClass1;

public class classTwo {
	public int balance;
	private TestClass1 otherClass;

	/*@
	  @ assignable balance, refClass.balance;
	  @*/
	public void initField() {
		balance = 1;
		otherClass.balance = 0;
	}
}
