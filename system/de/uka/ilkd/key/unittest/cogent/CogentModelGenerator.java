// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.cogent;

import java.util.*;
import java.io.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.unittest.*;

public class CogentModelGenerator implements DecProdModelGenerator{
    
    private SetOfTerm locations;
    private HashMap term2class;
    private CogentTranslation ct;

    public CogentModelGenerator(CogentTranslation ct, Services serv,
				HashMap term2class, SetOfTerm locations){
	this.ct = ct;	
	this.term2class = term2class;
	this.locations = locations;	
    }

    public Set createModels(){
	HashSet models = new HashSet();
	Model model = new Model(term2class);
	try{
	    String trans = ct.translate();
	    System.out.println("Cogent Input:\n"+trans);
	    //trans="!((from_account>=-2147483648) && (from_account<=2147483647) &&((2 + amount)>=-2147483648) && ((2 + amount)<=2147483647) &&(2>=-2147483648) && (2<=2147483647) &&(amount>=-2147483648) && (amount<=2147483647) &&(to_account>=-2147483648) && (to_account<=2147483647) &&((1 + amount)>=-2147483648) && ((1 + amount)<=2147483647) &&(1>=-2147483648) && (1<=2147483647) &&(amount>=-2147483648) && (amount<=2147483647) &&(to_account>=-2147483648) && (to_account<=2147483647) &&((-1 + from_account)>=-2147483648) && ((-1 + from_account)<=2147483647) &&(-1>=-2147483648) && (-1<=2147483647) &&(from_account>=-2147483648) && (from_account<=2147483647) &&(self>=-2147483648) && (self<=2147483647) &&(null<=0)&&(null>=0)  &&1 && (from_account >= (2 + amount)) && (to_account >= (1 + amount)) && (to_account <= (-1 + from_account))) || (0 || (self == null))";
	    //System.out.println("Overwritten Cogent Input:\n"+trans);
	    CogentResult response = 
		DecisionProcedureCogent.execute(trans);
	    System.out.println("Response:\n"+response.toString());
	    if(response.valid()){
		return models;
	    }
	    IteratorOfTerm it = locations.iterator();
	    while(it.hasNext()){
		Term t = it.next();
		EquivalenceClass ec = (EquivalenceClass) term2class.get(t);
		if(ec.isInt()){
		    model.setValue(ec, response.getValueForTerm(t, ct));
		}
	    }
	    models.add(model);
	}catch(IOException e){
	    throw new CogentException(e);
	}
	return models;
    }
}
