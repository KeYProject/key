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

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.UMLModelClass;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.speclang.SLTranslationError;



/**
 * The "BehaviouralSubtypingInv" proof obligation 
 * (formerly known as StructuralSubtyping). 
 */
public class BehaviouralSubtypingInvPO extends AbstractPO {
    
    private UMLModelClass subType;
    private ModelClass superType;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public BehaviouralSubtypingInvPO(UMLModelClass subType, 
                                     ModelClass superType) {
        super("BehaviouralSubtypingInv of " + subType.getClassName() + " and " 
              + superType.getClassName(),
              subType);
        this.subType    = subType;
        this.superType  = superType;
    }
    
    
    
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------    
        
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //make sure initConfig has been set
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        
        try {
        	//prepare self variable
	        LogicVariable selfVar = buildSelfVarAsLogicVar();
	               
	        //build conjunction of subtype invariants
	        Term subConjTerm = translateInvsOpen(subType.getMyClassInvariants(), 
	        				     selfVar);
	        
	        //build conjunction of supertype invariants
	        Term superConjTerm = translateInvsOpen(superType.getMyClassInvariants(),
	        				       selfVar);
	        
	        //build implication
	        Term impTerm = tb.imp(subConjTerm, superConjTerm);
	        
	        //build all-quantification
	        Term poTerm = tb.all(selfVar, impTerm);
	        poTerms = new Term[]{poTerm};
        } catch(SLTranslationError e) {
        	throw new ProofInputException(e);
        }
    }


    public Contractable[] getObjectOfContract() {
        return new Contractable[0];
    }

    
    public boolean initContract(Contract ct) {
        return false;
    }
}
