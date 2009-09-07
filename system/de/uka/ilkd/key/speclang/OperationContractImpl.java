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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
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
    private final KeYJavaType kjt;    
    private final ProgramMethod pm;
    private final Modality modality;
    private final Term originalPre;
    private final Term originalPost;
    private final Term originalMod;
    private final Term originalDep;    
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
	                          String name,
                                  KeYJavaType kjt,	                          
                                  ProgramMethod pm,
            		          Modality modality,
            		          Term pre,
            		          Term post,
            		          Term mod,
            		          Term dep,
            		          ProgramVariable selfVar,
            		          ImmutableList<ProgramVariable> paramVars,
            		          ProgramVariable resultVar,
            		          ProgramVariable excVar,
                                  Term heapAtPre,
                                  int id) {
	assert baseName != null;
        assert kjt != null;	
        assert pm != null;
        assert modality != null;
        assert pre != null;
        assert post != null;
        assert mod != null;
        assert (selfVar == null) == pm.isStatic();
        assert paramVars != null;
        assert paramVars.size() == pm.getParameterDeclarationCount();
        assert (resultVar == null) == (pm.getKeYJavaType() == null);
        assert excVar != null;
        assert heapAtPre != null;
        this.baseName               = baseName;
        this.name                   = name != null 
                                      ? name 
                                      : baseName + " [id: " + id + " / " + pm 
                                        + (kjt.equals(pm.getContainerType()) 
                                           ? "" 
                                           : " for " 
                                             + kjt.getJavaType().getName()) 
                                        + "]";
        this.pm          	    = pm;
        this.kjt                    = kjt;
        this.modality               = modality;
	this.originalPre            = pre;
	this.originalPost           = post;
	this.originalMod            = mod;
	this.originalDep            = dep;
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
     * @param mod the modifies clause of the contract
     * @param dep the depends clause of the contract     * 
     * @param selfVar the variable used for the receiver object
     * @param paramVars the variables used for the operation parameters
     * @param resultVar the variables used for the operation result
     * @param excVar the variable used for the thrown exception
     * @param heapAtPre the operator used for the pre-heap
     */
    public OperationContractImpl(String baseName,
                                 KeYJavaType kjt,	    
                                 ProgramMethod pm,
            		         Modality modality,
            		         Term pre,
            		         Term post,
            		         Term mod,
            		         Term dep,
            		         ProgramVariable selfVar,
            		         ImmutableList<ProgramVariable> paramVars,
            		         ProgramVariable resultVar,
            		         ProgramVariable excVar,
                                 Term heapAtPre) {
        this(baseName,
             null,
             kjt,             
             pm,
             modality,
             pre,
             post,
             mod,
             dep,
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
    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    @Override
    public ProgramMethod getTarget() {
        return pm;
    }
    

    @Override
    public OperationContract setID(int newId) {
        return new OperationContractImpl(baseName,
        	                         null,
                			 kjt,        	                         
                			 pm,
                			 modality,
                			 originalPre,
                			 originalPost,
                			 originalMod,
                			 originalDep,
                			 originalSelfVar,
                			 originalParamVars,
                			 originalResultVar,
                			 originalExcVar,
                			 originalHeapAtPre,
                			 newId);	
    }
    
    
    @Override
    public OperationContract setTarget(KeYJavaType newKJT,
	    			       ObserverFunction newPM, 
	    			       Services services) {
        return new OperationContractImpl(baseName,
        				 null,
                			 newKJT,        				 
                			 (ProgramMethod)newPM,
                			 modality,
                			 originalPre,
                			 originalPost,
                			 originalMod,
                			 originalDep,
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
	
        final String pre  = LogicPrinter.quickPrintTerm(originalPre, services);
        final String post = LogicPrinter.quickPrintTerm(originalPost, services);
        final String mod  = LogicPrinter.quickPrintTerm(originalMod, services);
        final String dep  = hasDep() 
                            ? LogicPrinter.quickPrintTerm(originalDep, services)
                            : null;
                      
        return "<html>"
                + "<i>" + LogicPrinter.escapeHTML(sig.toString()) + "</i>"
                + "<br><b>pre</b> "
                + LogicPrinter.escapeHTML(pre)
                + "<br><b>post</b> "
                + LogicPrinter.escapeHTML(post)
                + "<br><b>mod</b> "
                + LogicPrinter.escapeHTML(mod)
                + (hasDep() 
                   ? ""
                   :"<br><b>dep</b> " + LogicPrinter.escapeHTML(dep))
                + "<br><b>termination</b> "
                + getModality()
                + "</html>";
    }    
    
    
    @Override
    public Modality getModality() {
        return modality;
    }
    
    
    @Override
    public boolean hasDep() {
	return originalDep != null;
    }

    
    @Override
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
    public Term getPre(Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	Map replaceMap = new HashMap();
	replaceMap.put(TB.var(originalSelfVar), selfTerm);
	for(ProgramVariable paramVar : originalParamVars) {
	    replaceMap.put(TB.var(paramVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}
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
    public Term getMod(ProgramVariable selfVar, 
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
        return or.replace(originalMod);
    }
    
    
    @Override
    public Term getDep(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services) {
	assert hasDep();
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
	return or.replace(originalDep);
    }            
    
    
    @Override
    public Term getDep(Term heapTerm,
	               Term selfTerm,
	               ImmutableList<Term> paramTerms,
	               Services services) {
	assert hasDep();
	assert heapTerm != null;	
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
        if(originalDep == null) {
            return null;
        }        
	Map replaceMap = new HashMap();
	replaceMap.put(TB.heap(services), heapTerm);
	replaceMap.put(TB.var(originalSelfVar), selfTerm);
	for(ProgramVariable paramVar : originalParamVars) {
	    replaceMap.put(TB.var(paramVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}
	OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalDep);
    }    
        
    
    @Override
    public OperationContract union(OperationContract[] others, 
                                   String newName, 
                                   Services services) {
        assert others != null;
        for(OperationContract contract : others) {
            assert contract.getTarget().equals(pm);
        }
        if(others.length == 0) {
            return this;
        }
        
        //collect information
        Term pre = originalPre;
        Term post = TB.imp(atPreify(originalPre, originalHeapAtPre, services), 
        		   originalPost);
        Term mod = originalMod;
        Term dep = originalDep;
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
            Term otherMod = other.getMod(originalSelfVar, 
                                         originalParamVars, 
                                         services);
            Term otherDep = other.getDep(originalSelfVar, 
        	                         originalParamVars, 
        	                         services);

            pre = TB.or(pre, otherPre);
            post = TB.and(post, TB.imp(atPreify(otherPre, 
        	    				originalHeapAtPre, 
        	    				services), 
        	    		       otherPost));
            mod = TB.union(services, mod, otherMod);
            dep = TB.union(services, dep, otherDep);
        }

        return new OperationContractImpl(null,
        				 newName,
                                         kjt,        				 
                                         pm,
                                         modality,
                                         pre,
                                         post,
                                         mod,
                                         dep,
                                         originalSelfVar,
                                         originalParamVars,
                                         originalResultVar,
                                         originalExcVar,
                                         originalHeapAtPre,
                                         INVALID_ID);
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
        	                         name,
		 			 kjt,        	                         
		 			 pm,
		 			 modality,
		 			 TB.and(originalPre, addedPre),
		 			 originalPost,
		 			 originalMod,
		 			 originalDep,
		 			 originalSelfVar,
		 			 originalParamVars,
		 			 originalResultVar,
		 			 originalExcVar,
		 			 originalHeapAtPre,
		 			 id);
    }
    
    
    @Override
    public String toString() {
	return "pre: " 
		+ originalPre 
		+ "; post: " 
		+ originalPost 
		+ "; mod: " 
		+ originalMod
		+ "; dep: " 
		+ originalDep
		+ "; termination: "
		+ getModality();
    }
}
