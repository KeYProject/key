// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.DependencyContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Standard implementation of the DependencyContract interface.
 */
public final class DependencyContractImpl implements DependencyContract {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    final String baseName;    
    final String name;
    final KeYJavaType kjt;
    final IObserverFunction target;
    final KeYJavaType specifiedIn;
    final Term originalPre;
    final Term originalMby;    
    final Term originalDep;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final int id;    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    DependencyContractImpl(String baseName,
                           String name,
                           KeYJavaType kjt,
                           IObserverFunction target,
                           KeYJavaType specifiedIn,
                           Term pre,
                           Term mby,
                           Term dep,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           int id) {
	assert baseName != null;
	assert kjt != null;
	assert target != null;
	assert pre != null;
	assert dep != null : "cannot create contract "+baseName+" for "+target+" when no specification is given";
        assert (selfVar == null) == target.isStatic();
        assert paramVars != null;
        assert paramVars.size() == target.arity() - (target.isStatic() ? 1 : 2);
        assert pre.sort() == Sort.FORMULA;
	this.baseName = baseName;
        this.name = name != null 
                  ? name 
                  : ContractFactory.generateContractName(baseName, kjt, target,
                                       specifiedIn, id);
	this.kjt = kjt;
	this.target = target;
    this.specifiedIn = specifiedIn;
	this.originalPre = pre;
	this.originalMby = mby;	
	this.originalDep = dep;
	this.originalSelfVar = selfVar;
	this.originalParamVars = paramVars;
	this.id = id;
    }
    
    
    DependencyContractImpl(String baseName,
                           KeYJavaType kjt,
                           IObserverFunction target,
                           KeYJavaType specifiedIn,
                           Term pre,
                           Term mby,
                           Term dep,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars) {
	this(baseName, 
             null, 
             kjt, 
             target,
             specifiedIn,
             pre, 
             mby,             
             dep, 
             selfVar, 
             paramVars, 
             INVALID_ID);
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
    public IObserverFunction getTarget() {
	return target;
    }
    
    
    @Override
    public boolean hasMby() {
	return originalMby != null;
    }
    
    
    @Override
    public Term getPre(LocationVariable heap,
                       ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
	    	       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	if (originalSelfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(originalParamVar, paramVars.head());
	    paramVars = paramVars.tail();
	}
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalPre);
    }

    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
	    	       Services services) {
       Term result = null;
       for(LocationVariable heap : heapContext) {
          final Term p = getPre(heap, selfVar, paramVars, atPreVars, services);
          if(result == null) {
            result = p;
          }else{
            result = TB.and(result, p);
          }
       }
       return result;
    }
    
    
    @Override
    public Term getPre(LocationVariable heap,
                       Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Map<LocationVariable,Term> atPres,
	    	       Services services) {
	assert heapTerm != null;
	assert (selfTerm == null) == (originalSelfVar == null);
	assert paramTerms != null;
	assert paramTerms.size() == originalParamVars.size();
	assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	map.put(TB.getBaseHeap(services), heapTerm);
	if (originalSelfVar != null) {
            map.put(TB.var(originalSelfVar), selfTerm);
        }
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalPre);
    }
    

    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable,Term> heapTerms,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Map<LocationVariable,Term> atPres,
	    	       Services services) {
       Term result = null;
       for(LocationVariable heap : heapContext) {
          final Term p = getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);
          if(result == null) {
            result = p;
          }else{
            result = TB.and(result, p);
          }
       }
       return result;
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services) {
	assert hasMby();
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	if (originalSelfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(originalParamVar, paramVars.head());
	    paramVars = paramVars.tail();
	}
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalMby);
    }
    

    @Override
    public Term getMby(Term heapTerm,
	               Term selfTerm, 
	               ImmutableList<Term> paramTerms, 
	               Services services) {
	assert hasMby();
	assert heapTerm != null;
	assert (selfTerm == null) == (originalSelfVar == null);
	assert paramTerms != null;
	assert paramTerms.size() == originalParamVars.size();
	assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	map.put(TB.getBaseHeap(services), heapTerm);
	if (originalSelfVar != null) {
	    map.put(TB.var(originalSelfVar), selfTerm);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalMby);
    }    
   
    
    @Override
    public String getPlainText(Services services) {
       return getText(false, services);
    }
    
    @Override
    public String getHTMLText(Services services) {
       return getText(true, services);
    }
    
    private String getText(boolean includeHtmlMarkup, Services services) {
	     final String pre = LogicPrinter.quickPrintTerm(originalPre, services);
        final String mby = hasMby() 
        	           ? LogicPrinter.quickPrintTerm(originalMby, services)
        	           : null;
        final String dep = LogicPrinter.quickPrintTerm(originalDep, services);
        
        if (includeHtmlMarkup) {
           return "<html>"
                 + "<b>pre</b> "
                 + LogicPrinter.escapeHTML(pre, false)
                 + "<br><b>dep</b> "
                 + LogicPrinter.escapeHTML(dep, false)
                 + (hasMby() 
                    ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby, 
                                         false)
                    : "")                
                 + "</html>";
        }
        else {
           return "pre: "
                 + pre
                 + "\ndep: "
                 + dep
                 + (hasMby() ? "\nmeasured-by: " + mby : "");
        }
    }    
    
    
    @Override
    public boolean toBeSaved() {
	return false; //because dependency contracts currently cannot be
	              //specified directly in DL 
    }
    
    
    @Override
    public String proofToString(Services services) {
	assert false;
	return null;
    }
    

    @Override
    public Term getDep(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	if (originalSelfVar != null) {
	    map.put(originalSelfVar, selfVar);
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(originalParamVar, paramVars.head());
	    paramVars = paramVars.tail();
	}
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalDep);
    }
    

    @Override
    public Term getDep(Term heapTerm,
	               Term selfTerm, 
	               ImmutableList<Term> paramTerms, 
	               Services services) {
	assert heapTerm != null;
	assert (selfTerm == null) == (originalSelfVar == null);
	assert paramTerms != null;
	assert paramTerms.size() == originalParamVars.size();
	assert services != null;
	Map<SVSubstitute, SVSubstitute> map = new HashMap<SVSubstitute, SVSubstitute>();
	map.put(TB.getBaseHeap(services), heapTerm);
	if (originalSelfVar != null) {
            map.put(TB.var(originalSelfVar), selfTerm);
        }
	for(ProgramVariable originalParamVar : originalParamVars) {
	    map.put(TB.var(originalParamVar), paramTerms.head());
	    paramTerms = paramTerms.tail();
	}	
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalDep);
    }    
    
    
    @Override
    public String toString() {
	return originalDep.toString();
    }


    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, target,
                                                   specifiedIn, id);
    }


    @Override
    public VisibilityModifier getVisibility() {
	return null;
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
	    Contract contract) {
	return new DependencyContractPO(initConfig,
	        (DependencyContract) contract);
    }


    @Override
    public DependencyContract setID(int newId) {
        return new DependencyContractImpl(baseName,
                                          null,
                                          kjt,
                                          target,
                                          specifiedIn,
                                          originalPre,
                                          originalMby,
                                          originalDep,
                                          originalSelfVar,
                                          originalParamVars,
                                          newId);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
                              IObserverFunction newPM) {
        return new DependencyContractImpl(baseName,
                                          null,
                                          newKJT,
                                          newPM,
                                          specifiedIn,
                                          originalPre,
                                          originalMby,
                                          originalDep,
                                          originalSelfVar,
                                          originalParamVars,
                                          id);
    }
    
    
    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, target,
                                                        specifiedIn);
    }
}
