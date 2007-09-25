package de.uka.ilkd.key.unittest.simplify.ast;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.KeYParser;

public class NumberTerm extends Term{

    private int intValue;

    public NumberTerm(int i){
	super(""+i);
	intValue = i;
    }

    public String toSimplify(){
	return intValue+"";
    }

    public int getValue(){
	return intValue;
    }

    public de.uka.ilkd.key.logic.Term toZ(Services serv){
	return KeYParser.toZNotation(intValue+"", 
				     serv.getNamespaces().functions(),
				     TermFactory.DEFAULT);
    }

}
