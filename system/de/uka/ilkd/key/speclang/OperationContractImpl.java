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
    private final Term originalMby;    
    private final Term originalPost;
    private final Term originalMod;
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
            		          Term mby,
            		          Term post,
            		          Term mod,
            		          ProgramVariable selfVar,
            		          ImmutableList<ProgramVariable> paramVars,
            		          ProgramVariable resultVar,
            		          ProgramVariable excVar,
                                  Term heapAtPre,
                                  int id) {
	assert !(name == null && baseName == null);
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
	this.originalMby            = mby;
	this.originalPost           = post;
	this.originalMod            = mod;
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
     * @param mby the measured_by clause of the contract 
     * @param post the postcondition of the contract
     * @param mod the modifies clause of the contract
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
            		         Term mby,            		         
            		         Term post,
            		         Term mod,
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
             mby,
             post,
             mod,
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
	final Map<Term,Term> map = new HashMap<Term,Term>();
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
	final Map result = new LinkedHashMap();
	
        //self
	if(selfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
	    result.put(originalSelfVar, selfVar);
	}
	
        //parameters
	if(paramVars != null) {
	    assert originalParamVars.size() == paramVars.size();
	    final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
	    final Iterator<ProgramVariable> it2 = paramVars.iterator();
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
	    assert originalExcVar.sort().equals(excVar.sort());
	    result.put(originalExcVar, excVar);
	}
        
        //atPre-functions
	if(heapAtPre != null) {
	    assert originalHeapAtPre.sort().equals(heapAtPre.sort());
	    result.put(originalHeapAtPre, heapAtPre);
	}

	return result;
    }
    
    
    private Map /*Operator, Operator, Term -> Term*/ getReplaceMap(
	    		      Term heapTerm,
	    		      Term selfTerm, 
	    		      ImmutableList<Term> paramTerms, 
	    		      Term resultTerm, 
	    		      Term excTerm,
	    		      Term heapAtPre,
	    		      Services services) {
	final Map<Term,Term> result = new LinkedHashMap<Term,Term>();
	
	//heap
	assert heapTerm != null;
	assert heapTerm.sort().equals(services.getTypeConverter()
		                              .getHeapLDT()
		                              .targetSort());
	result.put(TB.heap(services), heapTerm);
	
        //self
	if(selfTerm != null) {
            assert selfTerm.sort().extendsTrans(originalSelfVar.sort());
	    result.put(TB.var(originalSelfVar), selfTerm);
	}
	
        //parameters
	if(paramTerms != null) {
	    assert originalParamVars.size() == paramTerms.size();
	    final Iterator<ProgramVariable> it1 = originalParamVars.iterator();
	    final Iterator<Term> it2 = paramTerms.iterator();
	    while(it1.hasNext()) {
		ProgramVariable originalParamVar = it1.next();
		Term paramTerm                   = it2.next();
		assert paramTerm.sort().extendsTrans(originalParamVar.sort());
		result.put(TB.var(originalParamVar), paramTerm);
	    }
	}
	
        //result
	if(resultTerm != null) {
	    assert originalResultVar.sort().equals(resultTerm.sort());
	    result.put(TB.var(originalResultVar), resultTerm);
	}
	
        //exception
	if(excTerm != null) {
	    assert originalExcVar.sort().equals(excTerm.sort());
	    result.put(TB.var(originalExcVar), excTerm);
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
    public boolean hasMby() {
	return originalMby != null;
    }
    
        
    @Override
    public Term getPre(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map replaceMap = getReplaceMap(selfVar, 
                                             paramVars, 
                                             null, 
                                             null,
                                             null, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPre);
    }
    
    
    @Override
    public Term getPre(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
	assert heapTerm != null;		
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	final Map replaceMap = getReplaceMap(heapTerm, 
					     selfTerm, 
					     paramTerms, 
					     null, 
					     null, 
					     null, 
					     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPre);
    }    
    
    
    @Override
    public Term getMby(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map replaceMap = getReplaceMap(selfVar, 
                                             paramVars, 
                                             null, 
                                             null,
                                             null, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalMby);
    }
    
    
    @Override
    public Term getMby(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
	assert heapTerm != null;		
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	final Map replaceMap = getReplaceMap(heapTerm, 
					     selfTerm, 
					     paramTerms, 
					     null, 
					     null, 
					     null, 
					     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalMby);
    }    
    

    @Override
    public OperationContract setID(int newId) {
        return new OperationContractImpl(baseName,
        	                         null,
                			 kjt,        	                         
                			 pm,
                			 modality,
                			 originalPre,
                			 originalMby,
                			 originalPost,
                			 originalMod,
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
                			 originalMby,
                			 originalPost,
                			 originalMod,
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
	} else if(pm.isConstructor()) {
	    sig.append(originalSelfVar);
	    sig.append(" = new ");
	}
	if(!pm.isStatic() && !pm.isConstructor()) {
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
        final String mby  = hasMby() 
        		    ? LogicPrinter.quickPrintTerm(originalMby, services)
        	            : null;        
        final String post = LogicPrinter.quickPrintTerm(originalPost, services);
        final String mod  = LogicPrinter.quickPrintTerm(originalMod, services);
                      
        return "<html>"
                + "<i>" + LogicPrinter.escapeHTML(sig.toString()) + "</i>"
                + "<br><b>pre</b> "
                + LogicPrinter.escapeHTML(pre)
                + "<br><b>post</b> "
                + LogicPrinter.escapeHTML(post)
                + "<br><b>mod</b> "
                + LogicPrinter.escapeHTML(mod)
                + (hasMby() 
                        ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby)
                        : "")                
                + "<br><b>termination</b> "
                + getModality()
                + "</html>";
    }    
    
    
    @Override
    public Modality getModality() {
        return modality;
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
	final Map replaceMap = getReplaceMap(selfVar, 
                                       	     paramVars, 
                                       	     resultVar, 
                                       	     excVar, 
                                       	     heapAtPre, 
                                       	     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPost);
    }
    
    
    @Override
    public Term getPost(Term heapTerm,
	                Term selfTerm, 
                        ImmutableList<Term> paramTerms, 
                        Term resultTerm, 
                        Term excTerm,
                        Term heapAtPre,
                        Services services) {
	assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert excTerm != null;
        assert heapAtPre != null;
        assert services != null;
	final Map replaceMap = getReplaceMap(heapTerm,
		                             selfTerm, 
                                             paramTerms, 
                                             resultTerm, 
                                             excTerm, 
                                       	     heapAtPre, 
                                       	     services);
	final OpReplacer or = new OpReplacer(replaceMap);
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
	final Map replaceMap = getReplaceMap(selfVar, 
                                             paramVars, 
                                             null, 
                                             null, 
                                             null, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(originalMod);
    }
    
    
    @Override    
    public Term getMod(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
	assert heapTerm != null;	
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	final Map replaceMap = getReplaceMap(heapTerm,
		                             selfTerm, 
                                             paramTerms, 
                                             null, 
                                             null, 
                                             null, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalMod);
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
        Term mby = originalMby;        
        Term post = TB.imp(atPreify(originalPre, originalHeapAtPre, services), 
        		   originalPost);
        Term mod = originalMod;
        for(OperationContract other : others) {
            Term otherPre = other.getPre(originalSelfVar, 
        	    			 originalParamVars, 
        	    			 services);
            Term otherMby = other.hasMby()
            		    ? other.getMby(originalSelfVar, 
            			           originalParamVars, 
            			           services)
            	            : null;   
            Term otherPost = other.getPost(originalSelfVar, 
        	    			   originalParamVars, 
        	    			   originalResultVar, 
        	    			   originalExcVar, 
        	    			   originalHeapAtPre, 
        	    			   services);
            Term otherMod = other.getMod(originalSelfVar, 
                                         originalParamVars, 
                                         services);

            pre = TB.or(pre, otherPre);
            mby = mby != null && otherMby != null
                  ? TB.ife(otherPre, otherMby, mby)
                  : null;            
            post = TB.and(post, TB.imp(atPreify(otherPre, 
        	    				originalHeapAtPre, 
        	    				services), 
        	    		       otherPost));
            mod = TB.union(services, mod, otherMod);
        }

        return new OperationContractImpl("invalid_name",
        				 newName,
                                         kjt,        				 
                                         pm,
                                         modality,
                                         pre,
                                         mby,
                                         post,
                                         mod,
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
		 			 originalMby,
		 			 originalPost,
		 			 originalMod,
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
		+ "; mby: " 
		+ originalMby
		+ "; post: " 
		+ originalPost 
		+ "; mod: " 
		+ originalMod
		+ "; termination: "
		+ getModality();
    }
}
