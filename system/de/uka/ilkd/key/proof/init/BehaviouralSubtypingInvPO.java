// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;



/**
 * The "BehaviouralSubtypingInv" proof obligation 
 * (formerly known as StructuralSubtyping). 
 */
public class BehaviouralSubtypingInvPO extends AbstractPO {
    
    private KeYJavaType subKJT;
    private KeYJavaType superKJT;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public BehaviouralSubtypingInvPO(InitConfig initConfig,
	    			     KeYJavaType subKJT, 
                                     KeYJavaType superKJT) {
        super(initConfig,
              "BehaviouralSubtypingInv of " + subKJT.getName() + " and " 
              + superKJT.getName(),
              subKJT);
        this.subKJT   = subKJT;
        this.superKJT = superKJT;
    }
    
    
    
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------    
        
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //prepare self variable
        LogicVariable selfVar = buildSelfVarAsLogicVar();
           
    	//build conjunction of subtype invariants
    	Term subConjTerm 
    		= translateInvsOpen(specRepos.getClassInvariants(subKJT), 
    			    	    selfVar);
        
        //build conjunction of supertype invariants
        Term superConjTerm = translateInvsOpen(specRepos.getClassInvariants(superKJT),
        				       selfVar);
        
        //build implication
        Term impTerm = TB.imp(subConjTerm, superConjTerm);
        
        //build all-quantification
        Term poTerm = TB.all(selfVar, impTerm);
        poTerms = new Term[]{poTerm};
    }
}
