//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.OperationContractImpl;
import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
import de.uka.ilkd.key.speclang.SetOfOperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * A factory for creating class invariants and operation contracts
 * from OCL specifications. This is the public interface to the 
 * ocl.translation package.
 */
public class OCLSpecFactory {
    
    private static final SignatureVariablesFactory SVF 
            = SignatureVariablesFactory.INSTANCE;
    
    private final Services services;
    private final OCLTranslator translator;
    
    private int invCounter;
    private int contractCounter;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public OCLSpecFactory(Services services) {
        assert services != null;
        this.services = services;
        this.translator = new OCLTranslator(services);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private String getInvName() {
        return "OCL class invariant (id: " + invCounter++ + ")";
    }
    
    
    private String getContractName() {
        return "OCL operation contract (id: " + contractCounter++ + ")";
    }

    
     
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
       
    public ClassInvariant createOCLClassInvariant(KeYJavaType kjt, 
                                                  String originalInv)
            throws SLTranslationException {
        assert kjt != null;
        assert originalInv != null;
        
        //create logical variable for self
        Sort sort = kjt.getSort();
        LogicVariable selfVar = new LogicVariable(new Name("self"), sort);
        
        //translate expression
        FormulaWithAxioms inv = translator.translateExpression(originalInv,
                                                               kjt,
                                                               selfVar,
                                                               null,
                                                               null,
                                                               null,
                                                               null);
        //all-quantify
        // dlohner: Not necessary (?), as ClassInvariantImpl.getClosedInv(..)
        // provides a closed version, where the original selfVar is replaced.
        // Also compare to JMLSpecFactory.createJMLClassInvariant(..).
        //inv = inv.allClose(services);

        //create invariant
        String name = getInvName();
        return new ClassInvariantImpl(name, 
                                      name,
                                      kjt, 
                                      inv,
                                      selfVar);
    }        
    
    
    public SetOfOperationContract createOCLOperationContracts(
                                            ProgramMethod programMethod,
                                            String originalPre,
                                            String originalPost,
                                            String originalModifies) 
            throws SLTranslationException {
        assert programMethod != null;
        
        //create variables for self, parameters, result, exception,
        //and the map for atPre-Functions
        ParsableVariable selfVar = SVF.createSelfVar(services, 
                                                     programMethod, 
                                                     false);
        ListOfParsableVariable paramVars = SVF.createParamVars(services, 
                                                               programMethod, 
                                                               false);
        ParsableVariable resultVar = SVF.createResultVar(services, 
                                                         programMethod, 
                                                         false);
        ParsableVariable excVar = SVF.createExcVar(services,
                                                   programMethod, 
                                                   false);
        Map<Operator, Function> atPreFunctions = new LinkedHashMap<Operator, Function>();
        
        //translate pre
        FormulaWithAxioms pre;
        if(originalPre == null) {
            pre = FormulaWithAxioms.TT;
        } else {
            pre = translator.translateExpression(originalPre,
                                                 programMethod.getContainerType(),
                                                 selfVar, 
                                                 paramVars, 
                                                 null, 
                                                 null, 
                                                 null);
        }
        
        //translate post
        FormulaWithAxioms post;
        if(originalPost == null) {
            post = FormulaWithAxioms.TT;
        } else {
            post = translator.translateExpression(originalPost, 
                                                  programMethod.getContainerType(),
                                                  selfVar, 
                                                  paramVars, 
                                                  resultVar, 
                                                  excVar, 
                                                  atPreFunctions);
        }
        
        //translate modifies
        SetOfLocationDescriptor modifies;
        if(originalModifies == null || originalModifies.equals("")) {
            modifies = EverythingLocationDescriptor.INSTANCE_AS_SET;
        } else {
            modifies = translator.translateModifiesExpression(originalModifies, 
                                                              selfVar, 
                                                              paramVars);
        }
        
        //create contracts
        SetOfOperationContract result = SetAsListOfOperationContract.EMPTY_SET;
        String name1 = getContractName();
        String name2 = getContractName();
        OperationContract contract1 
            =  new OperationContractImpl(name1,
                                         name1,
                                         programMethod,
                                         Modality.DIA,
                                         pre,
                                         post,
                                         modifies,
                                         selfVar,
                                         paramVars,
                                         resultVar,
                                         excVar,
                                         atPreFunctions);
        OperationContract contract2
            =  new OperationContractImpl(name2,
                                         name2,
                                         programMethod,
                                         Modality.BOX,
                                         pre,
                                         post,
                                         modifies,
                                         selfVar,
                                         paramVars,
                                         resultVar,
                                         excVar,
                                         atPreFunctions);
        result = result.add(contract1).add(contract2);
        return result;
    }
}
