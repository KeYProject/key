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

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IteratorOfParsableVariable;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the OperationContract interface.
 */
public class OperationContractImpl implements OperationContract {
    
    protected static final SignatureVariablesFactory SVN 
        = SignatureVariablesFactory.INSTANCE;
    
    private final String name;
    private final String displayName;
    private final ProgramMethod programMethod;
    private final Modality modality;
    private final FormulaWithAxioms originalPre;
    private final FormulaWithAxioms originalPost;
    private final SetOfLocationDescriptor originalModifies;
    private final ParsableVariable originalSelfVar;
    private final ListOfParsableVariable originalParamVars;
    private final ParsableVariable originalResultVar;
    private final ParsableVariable originalExcVar;
    private final Map /*Operator (normal) -> Function (atPre)*/ 
                                                    originalAtPreFunctions;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    /**
     * Creates an operation contract.
     * @param name the unique internal name of the contract
     * @param displayName the displayed name of the contract
     * @param programMethod the ProgramMethod to which the contract belongs
     * @param modality the modality of the contract
     * @param pre the precondition of the contract
     * @param post the postcondition of the contract
     * @param modifies the modifier set of the contract
     * @param selfVar the variable used for the receiver object
     * @param paramVars the variables used for the operation parameters
     * @param resultVar the variables used for the operation result
     * @param excVar the variable used for the thrown exception
     * @param atPreFunctions the functions used for atPre
     */
    public OperationContractImpl(String name,
                                 String displayName,
                                 ProgramMethod programMethod,
            		         Modality modality,
            		         FormulaWithAxioms pre,
            		         FormulaWithAxioms post,
            		         SetOfLocationDescriptor modifies,
            		         ParsableVariable selfVar,
            		         ListOfParsableVariable paramVars,
            		         ParsableVariable resultVar,
            		         ParsableVariable excVar,
                                 /*inout*/ Map /*Operator (normal) 
                                 -> Function (atPre)*/ atPreFunctions) {
        assert name != null && !name.equals("");
        assert displayName != null && !displayName.equals("");
        assert programMethod != null;
        assert modality != null;
        assert pre != null;
        assert post != null;
        assert modifies != null;
        assert (selfVar == null) == programMethod.isStatic();
        assert paramVars != null;
        assert paramVars.size() 
                == programMethod.getParameterDeclarationCount();
        assert (resultVar == null) == (programMethod.sort() == null);
        assert excVar != null;
        assert atPreFunctions != null;
        this.name                   = name;
        this.displayName            = displayName;
        this.programMethod          = programMethod;
        this.modality               = modality;
	this.originalPre            = pre;
	this.originalPost           = post;
	this.originalModifies       = modifies;
	this.originalSelfVar        = selfVar;
	this.originalParamVars      = paramVars;
	this.originalResultVar      = resultVar;
	this.originalExcVar         = excVar;
	this.originalAtPreFunctions = new LinkedHashMap();
        this.originalAtPreFunctions.putAll(atPreFunctions);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator -> Operator*/ getReplaceMap(
	    				ParsableVariable selfVar, 
	    				ListOfParsableVariable paramVars, 
	    				ParsableVariable resultVar, 
	    				ParsableVariable excVar,
                                        /*inout*/ Map /*Operator (normal) 
                                        -> Function (atPre)*/ atPreFunctions,
                                        Services services) {
	Map result = new LinkedHashMap();
	
        //self
	if(selfVar != null) {
	    assert originalSelfVar.sort().equals(selfVar.sort());
	    result.put(originalSelfVar, selfVar);
	}
	
        //parameters
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
	
        //result
	if(resultVar != null) {
	    assert originalResultVar.sort().equals(resultVar.sort());
	    result.put(originalResultVar, resultVar);
	}
	
        //exception
	if(excVar != null) {
	    assert originalExcVar.sort().equals(excVar.sort());
	    result.put(originalExcVar, excVar);
	}
        
        //atPre-functions
        if(atPreFunctions != null) {
            Iterator it = originalAtPreFunctions.entrySet().iterator();
            while(it.hasNext()) {
                Map.Entry entry = (Map.Entry) it.next();
                Operator originalNormalOp = (Operator) entry.getKey();
                Function originalAtPreFunc = (Function) entry.getValue();
                Operator normalOp = (Operator) result.get(originalNormalOp);
                if(normalOp == null) {
                    normalOp = originalNormalOp;
                }
                Function atPreFunc = (Function) atPreFunctions.get(normalOp);
                if(atPreFunc == null) {
                    atPreFunc 
                        = AtPreFactory.INSTANCE.createAtPreFunction(normalOp, 
                                                                    services);
                    atPreFunctions.put(normalOp, atPreFunc);
                    services.getNamespaces().functions().add(atPreFunc);                    
                }
                assert originalAtPreFunc.sort().equals(atPreFunc.sort());
                result.put(originalAtPreFunc, atPreFunc);
            }
        }
	
	return result;
    }
  
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    public String getName() {
        return name;
    }
    
    
    public String getDisplayName() {
        return displayName;
    }
    
    
    public ProgramMethod getProgramMethod() {
        return programMethod;
    }
    
    
    public Modality getModality() {
        return modality;
    }
    
    
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
	    			    ListOfParsableVariable paramVars,
                                    Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map replaceMap = getReplaceMap(selfVar, 
                                       paramVars, 
                                       null, 
                                       null,
                                       null, 
                                       services);
	OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPre);
    }

  
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     /*inout*/ Map /*Operator (normal) 
                                     -> Function (atPre)*/ atPreFunctions,
                                     Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert excVar != null;
        assert atPreFunctions != null;
        assert services != null;
	Map replaceMap = getReplaceMap(selfVar, 
                                       paramVars, 
                                       resultVar, 
                                       excVar, 
                                       atPreFunctions, 
                                       services);
	OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPost);
    }

  
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map replaceMap = getReplaceMap(selfVar, 
                                       paramVars, 
                                       null, 
                                       null, 
                                       null, 
                                       services);
	OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalModifies);
    }

    public String getHTMLText(Services services) {
        final String pre = LogicPrinter.quickPrintTerm(originalPre.getFormula(), 
                services);
        final String post = LogicPrinter.quickPrintTerm(originalPost.getFormula(), 
                services);
        final String locDesc = LogicPrinter.quickPrintLocationDescriptors(originalModifies, 
                services);
                      
        return "<html><b>pre</b> "
                + LogicPrinter.escapeHTML(pre)
                + "<br><b>post</b> "
                + LogicPrinter.escapeHTML(post)
                + "<br><b>modifies</b> "
                + LogicPrinter.escapeHTML(locDesc)
                + "<br><b>termination</b> "
                + getModality()
                + "</html>";
    }
    
    
    public String toString() {
	return "pre: " 
		+ originalPre 
		+ "; post: " 
		+ originalPost 
		+ "; modifies: " 
		+ originalModifies
		+ "; termination: "
		+ getModality();
    }
    
    
//    mbender
    public FormulaWithAxioms getOriginalPre() {
        return originalPre;
    }

    
    public FormulaWithAxioms getOriginalPost() {
        return originalPost;
    }
}
