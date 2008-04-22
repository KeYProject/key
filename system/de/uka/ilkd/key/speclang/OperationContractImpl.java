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

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
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
    private final FormulaWithAxioms originalWorkingSpacePost;
    private final Term originalWorkingSpace;
    private final SetOfLocationDescriptor originalModifies;
    private final ParsableVariable originalSelfVar;
    private final ListOfParsableVariable originalParamVars;
    private final ParsableVariable originalResultVar;
    private final ParsableVariable originalExcVar;
    private final Map<Operator, Function/* at pre */> originalAtPreFunctions;
    
    
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
                                 FormulaWithAxioms workingSpacePost,
            		         SetOfLocationDescriptor modifies,
                                 Term workingSpace,
            		         ParsableVariable selfVar,
            		         ListOfParsableVariable paramVars,
            		         ParsableVariable resultVar,
            		         ParsableVariable excVar,
                                 /*in*/ Map<Operator, Function> atPreFunctions) {
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
        this.name                     = name;
        this.displayName              = displayName;
        this.programMethod            = programMethod;
        this.modality                 = modality;
	this.originalPre              = pre;
	this.originalPost             = post;
        this.originalWorkingSpace     = workingSpace;
        this.originalWorkingSpacePost = workingSpacePost;
	this.originalModifies         = modifies;
	this.originalSelfVar          = selfVar;
	this.originalParamVars        = paramVars;
	this.originalResultVar        = resultVar;
	this.originalExcVar           = excVar;
	this.originalAtPreFunctions   = new LinkedHashMap<Operator, Function>();
        this.originalAtPreFunctions.putAll(atPreFunctions);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator -> Term*/<Term, Term> getReplaceMap(
                Term self, 
                ListOfTerm params, 
                Services services) {
        Map<Term, Term> result = new LinkedHashMap<Term, Term>();
        TermBuilder tb = TermBuilder.DF;   
        //self
        if(self != null) {
            assert self.sort().extendsTrans(originalSelfVar.sort());
            result.put(tb.var(originalSelfVar), self);
        }

        //parameters
        if(params != null) {
            assert originalParamVars.size() == params.size();
            IteratorOfParsableVariable it1 = originalParamVars.iterator();
            IteratorOfTerm it2 = params.iterator();
            while(it1.hasNext()) {
                ParsableVariable originalParamVar = it1.next();
                Term paramVar           = it2.next();
                assert paramVar.sort().extendsTrans(originalParamVar.sort());
                result.put(tb.var(originalParamVar), paramVar);
            }
        }
        return result;
    }
    
    
    private Map /*Operator -> Operator*/<Operator, Operator> getReplaceMap(
	    				ParsableVariable selfVar, 
	    				ListOfParsableVariable paramVars, 
	    				ParsableVariable resultVar, 
	    				ParsableVariable excVar,
                                        /*inout*/ Map< Operator, Function> atPreFunctions,
                                        Services services) {
	Map<Operator, Operator> result = new LinkedHashMap<Operator, Operator>();
	
        //self
	if(selfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
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
            Iterator<Map.Entry<Operator, Function>> it = 
                originalAtPreFunctions.entrySet().iterator();
            while(it.hasNext()) {
                Map.Entry<Operator,Function> entry = it.next();
                Operator originalNormalOp = entry.getKey();
                Function originalAtPreFunc = entry.getValue();
                Operator normalOp = result.get(originalNormalOp);
                if(normalOp == null) {
                    normalOp = originalNormalOp;
                }
                Function atPreFunc = atPreFunctions.get(normalOp);
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
	Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, 
                                       paramVars, 
                                       null, 
                                       null,
                                       null, 
                                       services);
	OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPre);
    }
    
    public FormulaWithAxioms getPre(Term self, 
                    ListOfTerm params,
                    Services services) {
        assert (self == null) == (originalSelfVar == null);
        assert params != null;
        assert params.size() == originalParamVars.size();
        assert services != null;
        Map<Term, Term> replaceMap = getReplaceMap(self, 
               params, 
               services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalPre);
    }
     
    public Term getWorkingSpace(Term self, 
            ListOfTerm params,
            Services services){
        assert (self == null) == (originalSelfVar == null);
        assert params != null;
        assert params.size() == originalParamVars.size();
        assert services != null;
        Map<Term, Term> replaceMap = getReplaceMap(self, 
                params, 
                services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalWorkingSpace);
    }
    
    public Term getWorkingSpace(ParsableVariable selfVar, 
                    ListOfParsableVariable paramVars,
                    Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, 
                paramVars, 
                null, 
                null,
                null, 
                services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalWorkingSpace);
    }

    
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     /*inout*/ Map<Operator, Function> atPreFunctions,
                                     Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert excVar != null;
        assert atPreFunctions != null;
        assert services != null;
	Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, 
                                       paramVars, 
                                       resultVar, 
                                       excVar, 
                                       atPreFunctions, 
                                       services);
	OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPost);
    }
    
    public FormulaWithAxioms getWorkingSpacePost(ParsableVariable selfVar, 
            ListOfParsableVariable paramVars, 
            ParsableVariable resultVar, 
            ParsableVariable excVar,
            /*inout*/ Map<Operator, Function> atPreFunctions,
            Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert excVar != null;
        assert atPreFunctions != null;
        assert services != null;
        Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, 
                paramVars, 
                resultVar, 
                excVar, 
                atPreFunctions, 
                services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalWorkingSpacePost);
    }

  
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<Operator, Operator> replaceMap = getReplaceMap(selfVar, 
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
        final String ws = originalWorkingSpace!=null? LogicPrinter.quickPrintTerm(originalWorkingSpace, 
                services) : "";
        final String locDesc = LogicPrinter.quickPrintLocationDescriptors(originalModifies, 
                services);
                      
        return "<html><b>pre</b> "
                + LogicPrinter.escapeHTML(pre)
                + "<br><b>post</b> "
                + LogicPrinter.escapeHTML(post)
                + "<br><b>modifies</b> "
                + LogicPrinter.escapeHTML(locDesc)
                + "<br><b>working space</b> "
                + LogicPrinter.escapeHTML(ws)
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
                + "; working space: "
                + (originalWorkingSpace!=null? originalWorkingSpace : "not specified")
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
