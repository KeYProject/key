// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
