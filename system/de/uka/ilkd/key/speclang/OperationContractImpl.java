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

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;


/**
 * Standard implementation of the OperationContract interface.
 */
public final class OperationContractImpl implements OperationContract {
    
    protected static final TermBuilder TB = TermBuilder.DF;
    protected static final SignatureVariablesFactory SVN 
        = SignatureVariablesFactory.INSTANCE;

    private final String name;
    private final String displayName;
    private final ProgramMethod programMethod;
    private final Modality modality;
    private final FormulaWithAxioms originalPre;
    private final FormulaWithAxioms originalPost;
    private final Term originalModifies;
    private final ProgramVariable originalSelfVar;
    private final ImmutableList<ProgramVariable> originalParamVars;
    private final ProgramVariable originalResultVar;
    private final ProgramVariable originalExcVar;
    private final Term originalHeapAtPre;
    
    
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
     * @param modifies the modifies clause of the contract
     * @param selfVar the variable used for the receiver object
     * @param paramVars the variables used for the operation parameters
     * @param resultVar the variables used for the operation result
     * @param excVar the variable used for the thrown exception
     * @param heapAtPre the operator used for the pre-heap
     */
    public OperationContractImpl(String name,
                                 String displayName,
                                 ProgramMethod programMethod,
            		         Modality modality,
            		         FormulaWithAxioms pre,
            		         FormulaWithAxioms post,
            		         Term modifies,
            		         ProgramVariable selfVar,
            		         ImmutableList<ProgramVariable> paramVars,
            		         ProgramVariable resultVar,
            		         ProgramVariable excVar,
                                 Term heapAtPre) {
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
        assert (resultVar == null) == (programMethod.getKeYJavaType() == null);
        assert excVar != null;
        assert heapAtPre != null;
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
	this.originalHeapAtPre      = heapAtPre;
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Map /*Operator, Operator, Term -> Term*/ getReplaceMap(
	    		      ProgramVariable selfVar, 
	    		      ImmutableList<ProgramVariable> paramVars, 
	    		      ProgramVariable resultVar, 
	    		      ProgramVariable excVar,
	    		      Term heapAtPre,
	    		      Services services) {
	Map result = new LinkedHashMap();
	
        //self
	if(selfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
	    result.put(originalSelfVar, selfVar);
	}
	
        //parameters
	if(paramVars != null) {
	    assert originalParamVars.size() == paramVars.size();
	    Iterator< ProgramVariable > it1 = originalParamVars.iterator();
	    Iterator< ProgramVariable > it2 = paramVars.iterator();
	    while(it1.hasNext()) {
		ProgramVariable originalParamVar = it1.next();
		ProgramVariable paramVar         = it2.next();
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
	    assert originalExcVar.sort().equals(excVar.sort())
		    || originalExcVar.sort().name().toString() //for backward compatibility with old DL contracts
		                     .equals("java.lang.Exception");
	    result.put(originalExcVar, excVar);
	}
        
        //atPre-functions
	if(heapAtPre != null) {
	    assert originalHeapAtPre.sort().equals(heapAtPre.sort());
	    result.put(originalHeapAtPre, heapAtPre);
	}

	return result;
    }
    
    
//    private ImmutableSet<LocationDescriptor> addGuard(ImmutableSet<LocationDescriptor> modifies, 
//                                             Term formula) {
//        ImmutableSet<LocationDescriptor> result 
//            = DefaultImmutableSet.<LocationDescriptor>nil();
//        for(LocationDescriptor loc : modifies) {
//            if(loc instanceof EverythingLocationDescriptor) {
//                return EverythingLocationDescriptor.INSTANCE_AS_SET;
//            } else {
//                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
//                Term newGuard = TB.and(bloc.getFormula(), formula);
//                result = result.add(new BasicLocationDescriptor(
//                        newGuard, 
//                        bloc.getLocTerm()));
//            }
//        }
//        return result;
//    }
//    
    
//    private FormulaWithAxioms atPreify(
//                FormulaWithAxioms fwa, 
//                /*inout*/Map<Operator, Function/*atPre*/> atPreFunctions,
//                Services services) {
//        APF.createAtPreFunctionsForTerm(fwa.getFormula(), 
//                                        atPreFunctions, 
//                                        services);
//        return new OpReplacer(atPreFunctions).replace(fwa);
//    }
//    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override
    public String getName() {
        return name;
    }
    
    
    @Override
    public String getDisplayName() {
        return displayName;
    }
    
    
    @Override
    public ProgramMethod getProgramMethod() {
        return programMethod;
    }
    
    
    @Override
    public Modality getModality() {
        return modality;
    }
    
    
    public FormulaWithAxioms getPre(ProgramVariable selfVar, 
	    			    ImmutableList< ProgramVariable > paramVars,
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

  
    @Override
    public FormulaWithAxioms getPost(ProgramVariable selfVar, 
                                     ImmutableList<ProgramVariable> paramVars, 
                                     ProgramVariable resultVar, 
                                     ProgramVariable excVar,
                                     Term heapAtPre,
                                     Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert excVar != null;
        assert heapAtPre != null;
        assert services != null;
	Map replaceMap = getReplaceMap(selfVar, 
                                       paramVars, 
                                       resultVar, 
                                       excVar, 
                                       heapAtPre, 
                                       services);
	OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPost);
    }

  
    @Override
    public Term getModifies(ProgramVariable selfVar, 
                            ImmutableList<ProgramVariable> paramVars,
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
    
    
    @Override
    public OperationContract union(OperationContract[] others, 
                                   String name, 
                                   String displayName, 
                                   Services services) {
	assert false : "not implemented";
	return null;
//        assert others != null;
//        for(OperationContract contract : others) {
//            assert contract.getProgramMethod().equals(programMethod);
//        }
//        if(others.length == 0) {
//            return this;
//        }
//        
//        //copy atPre map
//        Map<Operator, Function> newAtPreFunctions 
//            = new LinkedHashMap<Operator, Function>();
//        newAtPreFunctions.putAll(originalAtPreFunctions);
//
//        //collect information
//        FormulaWithAxioms pre = originalPre;
//        FormulaWithAxioms post = atPreify(originalPre, 
//                                          newAtPreFunctions, 
//                                          services).imply(originalPost);
////        ImmutableSet<LocationDescriptor> modifies = addGuard(originalModifies, 
////                                                    originalPre.getFormula());
//        Term modifies = originalModifies;
//        for(OperationContract other : others) {
//            FormulaWithAxioms otherPre = other.getPre(originalSelfVar, 
//                                                      originalParamVars, 
//                                                      services);
//            FormulaWithAxioms otherPost = other.getPost(originalSelfVar, 
//                                                        originalParamVars, 
//                                                        originalResultVar, 
//                                                        originalExcVar, 
//                                                        newAtPreFunctions, 
//                                                        services);
//            Term otherModifies 
//                    = other.getModifies(originalSelfVar, 
//                                        originalParamVars, 
//                                        services);
//
//            pre = pre.disjoin(otherPre);
//            post = post.conjoin(atPreify(otherPre, 
//                                         newAtPreFunctions, 
//                                         services).imply(otherPost));
////            modifies = modifies.union(addGuard(otherModifies, 
////                                      otherPre.getFormula()));
//            modifies = TB.union(services, modifies, otherModifies);
//        }
//
//        return new OperationContractImpl(name,
//                                         displayName,
//                                         programMethod,
//                                         modality,
//                                         pre,
//                                         post,
//                                         modifies,
//                                         originalSelfVar,
//                                         originalParamVars,
//                                         originalResultVar,
//                                         originalExcVar,
//                                         newAtPreFunctions);
    }
    
    
    public OperationContract replaceProgramMethod(ProgramMethod pm, 
	    					  Services services) {
        return new OperationContractImpl(name,
                			 displayName,
                			 pm,
                			 modality,
                			 originalPre,
                			 originalPost,
                			 originalModifies,
                			 originalSelfVar,
                			 originalParamVars,
                			 originalResultVar,
                			 originalExcVar,
                			 originalHeapAtPre);	
    }
    
    
    public OperationContract addPre(FormulaWithAxioms addedPre,
		    		    ParsableVariable selfVar, 
		    		    ImmutableList<ProgramVariable> paramVars,
		    		    Services services) {
	//replace in addedPre the variables used for self and parameters
	Map <Operator, Operator> map = new LinkedHashMap<Operator,Operator>();
	if(selfVar != null) {
	    map.put(selfVar, originalSelfVar);
	}
	if(paramVars != null) {
	    Iterator<ProgramVariable> it1 = paramVars.iterator();
	    Iterator<ProgramVariable> it2 = originalParamVars.iterator();
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
		 			 originalModifies,
		 			 originalSelfVar,
		 			 originalParamVars,
		 			 originalResultVar,
		 			 originalExcVar,
		 			 originalHeapAtPre);
    }

    
    @Override
    public String getHTMLText(Services services) {
	final StringBuffer sig = new StringBuffer();
//	sig.append("try { ");	
	if(originalResultVar != null) {
	    sig.append(originalResultVar);
	    sig.append(" = ");
	}
	if(originalSelfVar != null) {
	    sig.append(originalSelfVar);
	    sig.append(".");
	}
	sig.append(programMethod.getName());
	sig.append("(");
	for(ProgramVariable pv : originalParamVars) {
	    sig.append(pv.name());
	}
	sig.append(")");
	sig.append(" catch(");
	sig.append(originalExcVar);
	sig.append(")");
	
        final String pre 
        	= LogicPrinter.quickPrintTerm(originalPre.getFormula(), 
        				      services);
        final String post 
        	= LogicPrinter.quickPrintTerm(originalPost.getFormula(), 
        				      services);
        final String mod = LogicPrinter.quickPrintTerm(originalModifies, 
        					       services);
                      
        return "<html>"
                + "<i>" + LogicPrinter.escapeHTML(sig.toString()) + "</i>"
                + "<br><b>pre</b> "
                + LogicPrinter.escapeHTML(pre)
                + "<br><b>post</b> "
                + LogicPrinter.escapeHTML(post)
                + "<br><b>modifies</b> "
                + LogicPrinter.escapeHTML(mod)
                + "<br><b>termination</b> "
                + getModality()
                + "</html>";
    }
    
    
    @Override
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
}
