//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.IteratorOfLocationDescriptor;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.SetAsListOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfParsableVariable;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.proof.OpReplacer;


public class DLOperationContract extends AbstractOperationContract {
    private final Term originalPre;
    private final Term originalPost;
    private final SetOfLocationDescriptor originalModifies;
    private final ParsableVariable originalSelfVar;
    private final ListOfParsableVariable originalParamVars;
    private final ParsableVariable originalResultVar;
    private final ParsableVariable originalExcVar;
    private final Map /*Operator -> Term*/ axioms;
  
  
    public DLOperationContract(ModelMethod modelMethod,
            		       Modality modality,
            		       Term originalPre,
            		       Term originalPost,
            		       SetOfLocationDescriptor originalModifies,
            		       ParsableVariable originalSelfVar,
            		       ListOfParsableVariable originalParamVars,
            		       ParsableVariable originalResultVar,
            		       ParsableVariable originalExcVar,
            		       Map /*Operator -> Term*/ axioms) {
	super(modelMethod, modality);
	this.originalPre       = originalPre;
	this.originalPost      = originalPost;
	this.originalModifies  = originalModifies;
	this.originalSelfVar   = originalSelfVar;
	this.originalParamVars = originalParamVars;
	this.originalResultVar = originalResultVar;
	this.originalExcVar    = originalExcVar;
	this.axioms            = axioms;
    }
    
    
    private Map /*Operator -> Operator*/ getReplaceMap(
	    				ParsableVariable selfVar, 
	    				ListOfParsableVariable paramVars, 
	    				ParsableVariable resultVar, 
	    				ParsableVariable excVar) {
	Map result = new HashMap();
	
	if(selfVar != null) {
	    assert originalSelfVar.sort().equals(selfVar.sort());
	    result.put(originalSelfVar, selfVar);
	}
	
	if(paramVars != null) {
	    assert originalParamVars.size() == paramVars.size();
	    IteratorOfParsableVariable it1 = originalParamVars.iterator();
	    IteratorOfParsableVariable it2 = paramVars.iterator();
	    while(it1.hasNext()) {
		ParsableVariable originalParamVar = it1.next();
		ParsableVariable paramVar         = it2.next();
		assert originalParamVar.sort().equals(paramVar.sort());
		result.put(originalParamVar, paramVar);
	    }
	}
	
	if(resultVar != null) {
	    assert originalResultVar.sort().equals(resultVar.sort());
	    result.put(originalResultVar, resultVar);
	}
	
	if(excVar != null) {
	    assert originalExcVar.sort().equals(excVar.sort());
	    result.put(originalExcVar, excVar);
	}
	
	return result;
    }
      
    
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
	    			    ListOfParsableVariable paramVars,
                                    Services services) {
	Map replaceMap = getReplaceMap(selfVar, paramVars, null, null);
	OpReplacer or = new OpReplacer(replaceMap);
	
	return new FormulaWithAxioms(or.replace(originalPre), axioms);
    }

  
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     Services services) {
	Map replaceMap = getReplaceMap(selfVar, paramVars, resultVar, excVar);
	OpReplacer or = new OpReplacer(replaceMap);
	
	return new FormulaWithAxioms(or.replace(originalPost), axioms);
    }

  
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services) {
	Map replaceMap = getReplaceMap(selfVar, paramVars, null, null);
	OpReplacer or = new OpReplacer(replaceMap);
	
        SetOfLocationDescriptor result 
        	= SetAsListOfLocationDescriptor.EMPTY_SET;
        IteratorOfLocationDescriptor it = originalModifies.iterator();
        while(it.hasNext()) {
            LocationDescriptor loc = it.next();
            if(loc instanceof BasicLocationDescriptor) {
        	BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
        	Term unifiedFormula = or.replace(bloc.getFormula());
        	Term unifiedLocTerm = or.replace(bloc.getLocTerm());
        	result 
        	    = result.add(new BasicLocationDescriptor(unifiedFormula,
                                                             unifiedLocTerm));
            } else {
        	assert loc instanceof EverythingLocationDescriptor;
        	result = result.add(loc);
            }
        }
        
        return result;
    }
}
