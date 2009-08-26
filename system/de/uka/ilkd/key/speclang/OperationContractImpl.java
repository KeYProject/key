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

import java.util.HashMap;
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

    private final String baseName;
    private final String name;
    private final ProgramMethod pm;
    private final Modality modality;
    private final Term originalPre;
    private final Term originalPost;
    private final Term originalModifies;
    private final ProgramVariable originalSelfVar;
    private final ImmutableList<ProgramVariable> originalParamVars;
    private final ProgramVariable originalResultVar;
    private final ProgramVariable originalExcVar;
    private final Term originalHeapAtPre;
    private final int id;    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private OperationContractImpl(String baseName,
                                  ProgramMethod pm,
            		          Modality modality,
            		          Term pre,
            		          Term post,
            		          Term modifies,
            		          ProgramVariable selfVar,
            		          ImmutableList<ProgramVariable> paramVars,
            		          ProgramVariable resultVar,
            		          ProgramVariable excVar,
                                  Term heapAtPre,
                                  int id) {
        assert baseName != null && !baseName.equals("");
        assert pm != null;
        assert modality != null;
        assert pre != null;
        assert post != null;
        assert modifies != null;
        assert (selfVar == null) == pm.isStatic();
        assert paramVars != null;
        assert paramVars.size() == pm.getParameterDeclarationCount();
        assert (resultVar == null) == (pm.getKeYJavaType() == null);
        assert excVar != null;
        assert heapAtPre != null;
        this.baseName               = baseName;
        this.name                   = baseName + " [id: " + id + " / " + pm + "]";
        this.pm          	    = pm;
        this.modality               = modality;
	this.originalPre            = pre;
	this.originalPost           = post;
	this.originalModifies       = modifies;
	this.originalSelfVar        = selfVar;
	this.originalParamVars      = paramVars;
	this.originalResultVar      = resultVar;
	this.originalExcVar         = excVar;
	this.originalHeapAtPre      = heapAtPre;
	this.id                     = id;
    }    

    
    /**
     * Creates an operation contract.
     * @param baseName base name of the contract (does not have to be unique)
     * @param pm the ProgramMethod to which the contract belongs
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
    public OperationContractImpl(String baseName,
                                 ProgramMethod pm,
            		         Modality modality,
            		         Term pre,
            		         Term post,
            		         Term modifies,
            		         ProgramVariable selfVar,
            		         ImmutableList<ProgramVariable> paramVars,
            		         ProgramVariable resultVar,
            		         ProgramVariable excVar,
                                 Term heapAtPre) {
        this(baseName,
             pm,
             modality,
             pre,
             post,
             modifies,
             selfVar,
             paramVars,
             resultVar,
             excVar,
             heapAtPre,
             INVALID_ID);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private static Term atPreify(Term t, Term heapAtPre, Services services) {
	Map map = new HashMap();
	map.put(TB.heap(services), heapAtPre);
        return new OpReplacer(map).replace(t);
    }

    
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
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override
    public String getName() {
        return name;
    }
    

    @Override
    public int id() {
	return id;
    }
    
    
    @Override
    public ProgramMethod getProgramMethod() {
        return pm;
    }
    
    
    @Override
    public Modality getModality() {
        return modality;
    }
    
    
    public Term getPre(ProgramVariable selfVar, 
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
	return or.replace(originalPre);
    }

  
    @Override
    public Term getPost(ProgramVariable selfVar, 
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
                                   String newName, 
                                   Services services) {
        assert others != null;
        for(OperationContract contract : others) {
            assert contract.getProgramMethod().equals(pm);
        }
        if(others.length == 0) {
            return this;
        }
        
        //collect information
        Term pre = originalPre;
        Term post = TB.imp(atPreify(originalPre, originalHeapAtPre, services), 
        		   originalPost);
        Term modifies = originalModifies;
        for(OperationContract other : others) {
            Term otherPre = other.getPre(originalSelfVar, 
        	    			 originalParamVars, 
        	    			 services);
            Term otherPost = other.getPost(originalSelfVar, 
        	    			   originalParamVars, 
        	    			   originalResultVar, 
        	    			   originalExcVar, 
        	    			   originalHeapAtPre, 
        	    			   services);
            Term otherModifies = other.getModifies(originalSelfVar, 
                                        	   originalParamVars, 
                                        	   services);

            pre = TB.or(pre, otherPre);
            post = TB.and(post, TB.imp(atPreify(otherPre, 
        	    				originalHeapAtPre, 
        	    				services), 
        	    		       otherPost));
            modifies = TB.union(services, modifies, otherModifies);
        }

        return new OperationContractImpl(newName,
                                         pm,
                                         modality,
                                         pre,
                                         post,
                                         modifies,
                                         originalSelfVar,
                                         originalParamVars,
                                         originalResultVar,
                                         originalExcVar,
                                         originalHeapAtPre,
                                         OperationContract.INVALID_ID);
    }
    
    
    @Override
    public OperationContract setID(int newId) {
        return new OperationContractImpl(baseName,
                			 pm,
                			 modality,
                			 originalPre,
                			 originalPost,
                			 originalModifies,
                			 originalSelfVar,
                			 originalParamVars,
                			 originalResultVar,
                			 originalExcVar,
                			 originalHeapAtPre,
                			 newId);	
    }
    
    
    @Override
    public OperationContract setProgramMethod(ProgramMethod pm, 
	    				      Services services) {
        return new OperationContractImpl(baseName,
                			 pm,
                			 modality,
                			 originalPre,
                			 originalPost,
                			 originalModifies,
                			 originalSelfVar,
                			 originalParamVars,
                			 originalResultVar,
                			 originalExcVar,
                			 originalHeapAtPre,
                			 id);	
    }
    
    
    @Override
    public OperationContract addPre(Term addedPre,
		    		    ProgramVariable selfVar, 
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
        return new OperationContractImpl(baseName,
		 			 pm,
		 			 modality,
		 			 TB.and(originalPre, addedPre),
		 			 originalPost,
		 			 originalModifies,
		 			 originalSelfVar,
		 			 originalParamVars,
		 			 originalResultVar,
		 			 originalExcVar,
		 			 originalHeapAtPre,
		 			 id);
    }
    
    
    @Override
    public String getHTMLText(Services services) {
	final StringBuffer sig = new StringBuffer();
	if(originalResultVar != null) {
	    sig.append(originalResultVar);
	    sig.append(" = ");
	}
	if(originalSelfVar != null) {
	    sig.append(originalSelfVar);
	    sig.append(".");
	}
	sig.append(pm.getName());
	sig.append("(");
	for(ProgramVariable pv : originalParamVars) {
	    sig.append(pv.name());
	}
	sig.append(")");
	sig.append(" catch(");
	sig.append(originalExcVar);
	sig.append(")");
	
        final String pre = LogicPrinter.quickPrintTerm(originalPre, services);
        final String post = LogicPrinter.quickPrintTerm(originalPost, services);
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
