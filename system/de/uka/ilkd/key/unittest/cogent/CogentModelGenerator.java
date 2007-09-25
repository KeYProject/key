// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
	    CogentResult response = 
		DecisionProcedureCogent.execute(ct.translate());
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
