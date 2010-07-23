// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.*;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the OperationContract interface.
 */
public final class OperationContractImpl implements OperationContract {
    
    protected static final TermBuilder TB = TermBuilder.DF;
    protected static final SignatureVariablesFactory SVN 
        = SignatureVariablesFactory.INSTANCE;
    protected static final AtPreFactory APF = AtPreFactory.INSTANCE;

    private final String name;
    private final String displayName;
    private final ProgramMethod programMethod;
    private final Modality modality;
    private final FormulaWithAxioms originalPre;
    private final FormulaWithAxioms originalWorkingSpacePost;
    private final Term originalWorkingSpace;
    private final FormulaWithAxioms originalPost;
    private final ImmutableSet<LocationDescriptor> originalModifies;
    private final ParsableVariable originalSelfVar;
    private final ImmutableList<ParsableVariable> originalParamVars;
    private final ParsableVariable originalResultVar;
    private final ParsableVariable originalExcVar;
    private final Map<Operator, Function/* atPre */> originalAtPreFunctions;
    
    
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
            		         ImmutableSet<LocationDescriptor> modifies,
                                 Term workingSpace,                                 
            		         ParsableVariable selfVar,
            		         ImmutableList<ParsableVariable> paramVars,
            		         ParsableVariable resultVar,
            		         ParsableVariable excVar,
                                 /*in*/ Map<Operator, Function /*atPre*/> atPreFunctions) {
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
                ImmutableList<Term> params, 
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
            Iterator<ParsableVariable> it1 = originalParamVars.iterator();
            Iterator<Term> it2 = params.iterator();
            while(it1.hasNext()) {
                ParsableVariable originalParamVar = it1.next();
                Term paramVar           = it2.next();
                assert paramVar.sort().extendsTrans(originalParamVar.sort());
                result.put(tb.var(originalParamVar), paramVar);
            }
        }
        return result;
    }
    
    private Map /*Operator -> Term*/<Term, Term> getReplaceMap(
            ParsableVariable self, 
            Term memoryArea,
            ImmutableList<ParsableVariable> paramVars,
            Services services) {
        Map<Term, Term> result = new LinkedHashMap<Term, Term>();
        TermBuilder tb = TermBuilder.DF;   
        //self
        if(self != null) {
            assert self.sort().extendsTrans(originalSelfVar.sort());
            result.put(tb.var(originalSelfVar), tb.var(self));
        }
        
        //memory area
        if(memoryArea != null) {
            assert memoryArea.sort().extendsTrans(services.getJavaInfo().getDefaultMemoryArea().sort());
            result.put(tb.var(services.getJavaInfo().getDefaultMemoryArea()), memoryArea);
        }
    
        //parameters
        if(paramVars != null) {
            assert originalParamVars.size() == paramVars.size();
            Iterator<ParsableVariable> it1 = originalParamVars.iterator();
            Iterator<ParsableVariable> it2 = paramVars.iterator();
            while(it1.hasNext()) {
                ParsableVariable originalParamVar = it1.next();
                ParsableVariable paramVar           = it2.next();
                assert paramVar.sort().extendsTrans(originalParamVar.sort());
                result.put(tb.var(originalParamVar), tb.var(paramVar));
            }
        }
        return result;
    }    
    
    private Map <Operator, Operator> getReplaceMap(
	    				ParsableVariable selfVar, 
	    				ImmutableList<ParsableVariable> paramVars, 
	    				ParsableVariable resultVar, 
	    				ParsableVariable excVar,
                                        /*inout*/ Map< Operator, Function/*atPre*/> atPreFunctions,
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
	    Iterator<ParsableVariable> it1 = originalParamVars.iterator();
	    Iterator<ParsableVariable> it2 = paramVars.iterator();
	    while(it1.hasNext()) {
		ParsableVariable originalParamVar = it1.next();
		ParsableVariable paramVar         = it2.next();
		assert originalParamVar.sort().equals(paramVar.sort()) : originalParamVar.sort() + " does not equal " + paramVar.sort();
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
	    assert originalExcVar.sort().equals(excVar.sort())
		    || originalExcVar.sort().name().toString() //for backward compatibility with old DL contracts
		                     .equals("java.lang.Exception");
	    result.put(originalExcVar, excVar);
	}
        
        //atPre-functions
        if(atPreFunctions != null) {
            for (Object o : originalAtPreFunctions.entrySet()) {
                Map.Entry<Operator, Function> entry = (Map.Entry<Operator, Function>) o;
                Operator originalNormalOp = entry.getKey();
                Function originalAtPreFunc = entry.getValue();
                Operator normalOp = result.get(originalNormalOp);
                if (normalOp == null) {
                    normalOp = originalNormalOp;
                }
                Function atPreFunc = atPreFunctions.get(normalOp);
                if (atPreFunc == null) {
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
    
    
    private ImmutableSet<LocationDescriptor> addGuard(ImmutableSet<LocationDescriptor> modifies, 
                                             Term formula) {
        ImmutableSet<LocationDescriptor> result 
            = DefaultImmutableSet.<LocationDescriptor>nil();
        for(LocationDescriptor loc : modifies) {
            if(loc instanceof EverythingLocationDescriptor) {
                return EverythingLocationDescriptor.INSTANCE_AS_SET;
            } else {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                Term newGuard = TB.and(bloc.getFormula(), formula);
                result = result.add(new BasicLocationDescriptor(
                        newGuard, 
                        bloc.getLocTerm()));
            }
        }
        return result;
    }
    
    
    private FormulaWithAxioms atPreify(
                FormulaWithAxioms fwa, 
                /*inout*/Map<Operator, Function/*atPre*/> atPreFunctions,
                Services services) {
        APF.createAtPreFunctionsForTerm(fwa.getFormula(), 
                                        atPreFunctions, 
                                        services);
        return new OpReplacer(atPreFunctions).replace(fwa);
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
	    			    ImmutableList<ParsableVariable> paramVars,
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
    
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
                        ImmutableList<ParsableVariable> paramVars,
                        Term memoryArea,
                        Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
        Map<Term, Term> replaceMap = getReplaceMap(selfVar, 
                memoryArea,
                paramVars, 
                services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalPre);
    }
    
    public FormulaWithAxioms getPre(Term self, 
                    ImmutableList<Term> params,
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
            ImmutableList<Term> params,
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
                    ImmutableList<ParsableVariable> paramVars,
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
                                     ImmutableList<ParsableVariable> paramVars, 
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
    
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
            ImmutableList<ParsableVariable> paramVars, 
            ParsableVariable resultVar, 
            ParsableVariable excVar,
            Term memoryArea,
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
        Map<Term, Term> replaceMap2 = getReplaceMap(selfVar, 
                memoryArea,
                paramVars, 
                services);
        OpReplacer or2 = new OpReplacer(replaceMap2);
        return or2.replace(or.replace(originalPost));
    }
    
    public FormulaWithAxioms getWorkingSpacePost(ParsableVariable selfVar, 
            ImmutableList<ParsableVariable> paramVars, 
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

  
    public ImmutableSet<LocationDescriptor> getModifies(ParsableVariable selfVar, 
                                               ImmutableList<ParsableVariable> paramVars,
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
        return or.replaceLoc(originalModifies);
    }
    
    
    public OperationContract union(OperationContract[] others, 
                                   String p_name, 
                                   String p_displayName, 
                                   Services services) {
        assert others != null;
        for(OperationContract contract : others) {
            assert contract.getProgramMethod().equals(programMethod);
        }
        if(others.length == 0) {
            return this;
        }
        
        //copy atPre map
        Map<Operator, Function> newAtPreFunctions 
            = new LinkedHashMap<Operator, Function>();
        newAtPreFunctions.putAll(originalAtPreFunctions);

        //collect information
        FormulaWithAxioms pre = originalPre;
        FormulaWithAxioms post = atPreify(originalPre, 
                                          newAtPreFunctions, 
                                          services).imply(originalPost);

	FormulaWithAxioms wsPost = atPreify(originalPre, 
                                          newAtPreFunctions, 
					    services).imply(originalWorkingSpacePost);
        ImmutableSet<LocationDescriptor> modifies = addGuard(originalModifies, 
                                                    originalPre.getFormula());
	
	Term[] argTerms = new Term[originalParamVars.size()+(programMethod.isStatic()?0:1)];
	int i = 0;
	if(!programMethod.isStatic()){
	    argTerms[i++] = TB.var((ProgramVariable) originalSelfVar);
	}
	for(ParsableVariable var : originalParamVars){
	    argTerms[i++] = TB.var((ProgramVariable) var);
	}
	
	Term ws = TB.tf().createWorkingSpaceNonRigidTerm(programMethod, 
							 (Sort) services.getNamespaces().
							 sorts().lookup(new Name("int")),
							 argTerms);
	ws = TB.ife(pre.getFormula(), originalWorkingSpace, ws);

        for(OperationContract other : others) {
            FormulaWithAxioms otherPre = other.getPre(originalSelfVar, 
                                                      originalParamVars, 
                                                      services);
            FormulaWithAxioms otherPost = other.getPost(originalSelfVar, 
                                                        originalParamVars, 
                                                        originalResultVar, 
                                                        originalExcVar, 
                                                        newAtPreFunctions, 
                                                        services);

            FormulaWithAxioms otherWSPost = other.getWorkingSpacePost(originalSelfVar, 
								      originalParamVars, 
								      originalResultVar, 
								      originalExcVar, 
								      newAtPreFunctions, 
								      services);

	    Term otherWS = other.getWorkingSpace(originalSelfVar, 
						 originalParamVars, 
						 services);
	    ws = TB.ife(otherPre.getFormula(), otherWS, ws);

            ImmutableSet<LocationDescriptor> otherModifies 
                    = other.getModifies(originalSelfVar, 
                                        originalParamVars, 
                                        services);

            pre = pre.disjoin(otherPre);
            post = post.conjoin(atPreify(otherPre, 
                                         newAtPreFunctions, 
                                         services).imply(otherPost));
            wsPost = wsPost.conjoin(atPreify(otherPre, 
					     newAtPreFunctions, 
					     services).imply(otherWSPost));
            modifies = modifies.union(addGuard(otherModifies, 
                                      otherPre.getFormula()));

        }

        return new OperationContractImpl(p_name,
                                         p_displayName,
                                         programMethod,
                                         modality,
                                         pre,
                                         post,
					 wsPost,
                                         modifies,
					 ws,					 
                                         originalSelfVar,
                                         originalParamVars,
                                         originalResultVar,
                                         originalExcVar,
                                         newAtPreFunctions);
    }
    
    public OperationContract replaceProgramMethod(ProgramMethod pm, 
	    					  Services services) {
        return new OperationContractImpl(name,
                			 displayName,
                			 pm,
                			 modality,
                			 originalPre,
                			 originalPost,
					 originalWorkingSpacePost,
                			 originalModifies,
					 originalWorkingSpace,					 
                			 originalSelfVar,
                			 originalParamVars,
                			 originalResultVar,
                			 originalExcVar,
                			 originalAtPreFunctions);	
    }
    
    
    public OperationContract addPre(FormulaWithAxioms addedPre,
		    		    ParsableVariable selfVar, 
		    		    ImmutableList<ParsableVariable> paramVars,
		    		    Services services) {
	//replace in addedPre the variables used for self and parameters
	Map <Operator, Operator> map = new LinkedHashMap<Operator,Operator>();
	if(selfVar != null) {
	    map.put(selfVar, originalSelfVar);
	}
	if(paramVars != null) {
	    Iterator<ParsableVariable> it1 = paramVars.iterator();
	    Iterator<ParsableVariable> it2 = originalParamVars.iterator();
	    while(it1.hasNext()) {
		assert it2.hasNext();
		map.put(it1.next(), it2.next());
	    }
	}
	OpReplacer or = new OpReplacer(map);
	addedPre = or.replace(addedPre);
	
	//create new contract
        return new OperationContractImpl(name,
		 			 displayName,
		 			 programMethod,
		 			 modality,
		 			 originalPre.conjoin(addedPre),
		 			 originalPost,
					 originalWorkingSpacePost,
		 			 originalModifies,
					 originalWorkingSpace,
		 			 originalSelfVar,
		 			 originalParamVars,
		 			 originalResultVar,
		 			 originalExcVar,
		 			 originalAtPreFunctions);
    }
    
    public ImmutableSet<LocationDescriptor> getModifies(ParsableVariable self, 
            Term memoryArea,
            ImmutableList<ParsableVariable> params,
            Services services) {
        assert (self == null) == (originalSelfVar == null);
        assert params != null;
        assert params.size() == originalParamVars.size();
        assert services != null;
        Map<Term, Term> replaceMap = getReplaceMap(self, 
                memoryArea,
                params, 
                services);
        OpReplacer or = new OpReplacer(replaceMap);
        return or.replaceLoc(originalModifies);
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
