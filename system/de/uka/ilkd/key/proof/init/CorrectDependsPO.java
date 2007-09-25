// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.SLTranslationError;
import de.uka.ilkd.key.util.Debug;


/**
 * The "CorrectDependsPO" proof obligation. 
 */
public class CorrectDependsPO extends AbstractPO {
    
    private final SetOfLocationDescriptor dependsClause;
    private final ClassInvariant inv;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public CorrectDependsPO(SetOfLocationDescriptor dependsClause,
                            ClassInvariant inv) {
        super("CorrectDepends of \"" + inv + "\"", 
              inv.getModelClass());
        this.dependsClause = dependsClause;
        this.inv           = inv;
    }
        
    
    
    //-------------------------------------------------------------------------    
    //local helper methods
    //-------------------------------------------------------------------------
    

    private Update createUpdate(UpdateFactory uf, Map atPreFunctions) {
        Update result = uf.skip();
        
        IteratorOfLocationDescriptor it = dependsClause.iterator();
        while(it.hasNext()) {
            LocationDescriptor loc = it.next();
            Debug.assertTrue(loc instanceof BasicLocationDescriptor);
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            
            Term guardTerm = bloc.getFormula();
            Term locTerm = bloc.getLocTerm();
            
            createAtPreFunctionsForTerm(guardTerm, atPreFunctions);
            createAtPreFunctionsForTerm(locTerm, atPreFunctions);
            
            Term[] subTermsAtPre = new Term[locTerm.arity()];
            ArrayOfQuantifiableVariable[] boundVars 
                = new ArrayOfQuantifiableVariable[locTerm.arity()];
            for(int i = 0; i < locTerm.arity(); i++) {
                subTermsAtPre[i] = replaceOps(atPreFunctions, locTerm.sub(i)); 
                boundVars[i] = locTerm.varsBoundHere(i);
            }
            Term locAtIntermediateTerm = tf.createTerm(locTerm.op(),
                                                       subTermsAtPre,
                                                       boundVars,
                                                       null);
            
            Term locAtPreTerm = replaceOps(atPreFunctions, locTerm);
            Update elementaryUpdate = uf.elementaryUpdate(locAtIntermediateTerm, 
                                                          locAtPreTerm);
            
            Term guardAtPreTerm = replaceOps(atPreFunctions, guardTerm);
            Update guardedUpdate = uf.guard(guardAtPreTerm, elementaryUpdate);
            
            Update quantifiedUpdate = guardedUpdate;
            IteratorOfQuantifiableVariable it2 = locTerm.freeVars().iterator();
            while(it2.hasNext()) {
                quantifiedUpdate = uf.quantify(it2.next(), quantifiedUpdate);
            }
            
            result = uf.sequential(result, quantifiedUpdate);
        }

        return result;
    }
    
    
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------        
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //make sure initConfig has been set
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
 
        //prepare container for @pre-functions
        Map atPreFunctions = new HashMap();
        
        try {
        	//translate invariant
	        Term invTerm = translateInv(inv);
	                                       
	        //build post term
	        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
	        Term updateTerm = uf.apply(createUpdate(uf, atPreFunctions), invTerm);
	        AnonymousUpdate au = AnonymousUpdate.getNewAnonymousOperator();
	        Term postTerm = tf.createAnonymousUpdateTerm(au, 
	                                                     updateTerm);
	        
	        //build pre term
	        Term atPreDefinitionsTerm = buildAtPreDefinitions(atPreFunctions);
	        Term preTerm = tf.createJunctorTerm(Op.AND, 
	                                            atPreDefinitionsTerm, 
	                                            invTerm);
	
	        //build implication
	        Term poTerm = tf.createJunctorTerm(Op.IMP, preTerm, postTerm);
	        poTerms = new Term[]{poTerm};
        } catch (SLTranslationError e) {
        	throw new ProofInputException(e);
        }
	        
        //register everything in namespaces
        registerInNamespaces(atPreFunctions);
    }


    public Contractable[] getObjectOfContract() {
        return new Contractable[0];
    }

    
    public boolean initContract(Contract ct) {
        return false;
    }
    
    
    //-------------------------------------------------------------------------
    
    protected Term getTerm() {
        return poTerms[0];
    }
}
