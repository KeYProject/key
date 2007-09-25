package de.uka.ilkd.key.unittest;

public class UnitTestException extends RuntimeException{
  
    public UnitTestException(String s){
	super(s);
    }

    public UnitTestException(Exception e){
	super(e);
    }

}
