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

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * Standard implementation of the OperationContract interface.
 */
public class FunctionalOperationContractImpl implements FunctionalOperationContract {
    
    protected static final TermBuilder TB = TermBuilder.DF;

    final String baseName;
    final String name;
    final KeYJavaType kjt;
    final IProgramMethod pm;
    final KeYJavaType specifiedIn;
    final Modality modality;
    final Map<LocationVariable,Term> originalPres;
    final Term originalMby;
    final Map<LocationVariable,Term> originalPosts;
    final Map<LocationVariable,Term> originalMods;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final ProgramVariable originalResultVar;
    final ProgramVariable originalExcVar;
    final Map<LocationVariable,LocationVariable> originalAtPreVars;
    final int id;
    final boolean transaction;
    final boolean toBeSaved;
    
    /**
     * If a method is strictly pure, it has no modifies clause which could
     * anonymised.
     * @see #hasModifiesClause()
     */
    final boolean hasRealModifiesClause;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    FunctionalOperationContractImpl(String baseName,
                                    String name,
                                    KeYJavaType kjt,
                                    IProgramMethod pm,
                                    KeYJavaType specifiedIn,
                                    Modality modality,
                                    Map<LocationVariable,Term> pres,
                                    Term mby,
                                    Map<LocationVariable,Term> posts,
                                    Map<LocationVariable,Term> mods,
                                    boolean hasRealMod,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable resultVar,
                                    ProgramVariable excVar,
                                    Map<LocationVariable, LocationVariable> atPreVars,
                                    int id,
                                    boolean toBeSaved,
                                    boolean transaction) {
        assert !(name == null && baseName == null);
        assert kjt != null;	
        assert pm != null;
        assert pres != null;
        assert posts != null;
        assert modality != null;
        assert (selfVar == null) == pm.isStatic();
        assert paramVars != null;
        assert paramVars.size() == pm.getParameterDeclarationCount();
        if (resultVar == null){
            assert (pm.isVoid() || pm.isConstructor()) : "resultVar == null for method "+pm;
        } else {
            assert (!pm.isVoid() && !pm.isConstructor()) : "non-null result variable for void method or constructor "+pm+" with return type "+pm.getReturnType();
        }
        assert excVar != null;
        assert atPreVars.size() != 0;
        this.baseName               = baseName;
        this.name = name != null 
                  ? name 
                  : ContractFactory.generateContractName(baseName, kjt, pm, specifiedIn, id);
        this.pm          	    = pm;
        this.kjt                    = kjt;
        this.specifiedIn            = specifiedIn;
        this.modality               = modality;
        this.originalPres           = pres;
        this.originalMby            = mby;
        this.originalPosts          = posts;
        this.originalMods           = mods;
        this.hasRealModifiesClause  = hasRealMod;
        this.originalSelfVar        = selfVar;
        this.originalParamVars      = paramVars;
        this.originalResultVar      = resultVar;
        this.originalExcVar         = excVar;
        this.originalAtPreVars      = atPreVars;
        this.id                     = id;
        this.transaction            = transaction;
        this.toBeSaved	            = toBeSaved;
    }
  
    
    /**
     * Creates an operation contract.
     * @param baseName base name of the contract (does not have to be unique)
     * @param pm the IProgramMethod to which the contract belongs
     * @param modality the modality of the contract
     * @param pre the precondition of the contract
     * @param mby the measured_by clause of the contract 
     * @param post the postcondition of the contract
     * @param mod the modifies clause of the contract
     * @param selfVar the variable used for the receiver object
     * @param paramVars the variables used for the operation parameters
     * @param resultVar the variables used for the operation result
     * @param excVar the variable used for the thrown exception
     * @param heapAtPreVar the variable used for the pre-heap
     */
    FunctionalOperationContractImpl(String baseName,
                                    KeYJavaType kjt,
                                    IProgramMethod pm,
                                    KeYJavaType specifiedIn,
                                    Modality modality,
                                    Map<LocationVariable,Term> pres,
                                    Term mby,
                                    Map<LocationVariable,Term> posts,
                                    Map<LocationVariable,Term> mods,
                                    boolean hasMod,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    ProgramVariable resultVar,
                                    ProgramVariable excVar,
                                    Map<LocationVariable, LocationVariable> atPreVars,
                                    boolean toBeSaved,
                                    boolean transaction) {
        this(baseName,
             null,
             kjt,             
             pm,
             specifiedIn,
             modality,
             pres,
             mby,
             posts,
             mods,
             hasMod,
             selfVar,
             paramVars,
             resultVar,
             excVar,
             atPreVars,
             INVALID_ID,
             toBeSaved,
             transaction);
    }
    
    
    /* *
     * Creates an operation contract.
     * 
     * @param baseName base name of the contract (does not have to be unique)
     * @param pm 	the IProgramMethod to which the contract belongs
     * @param modality the modality of the contract
     * @param pre 	the precondition of the contract
     * @param mby 	the measured_by clause of the contract 
     * @param post 	the postcondition of the contract
     * @param mod 	the modifies clause of the contract
     * @param progVars collection of variables for the receiver object,
     * 			operation parameters, operation result, thrown exception
     * 			and the pre-heap
     */
//    FunctionalOperationContractImpl(String baseName, IProgramMethod pm,
//	    Modality modality, Term pre, Term mby, Term post, Term mod, boolean hasMod, Term modBackup,
//	    ProgramVariableCollection progVars, boolean toBeSaved) {
//	this(baseName, null, pm.getContainerType(), pm, modality, pre, mby,
//	        post, mod, hasMod, modBackup, progVars.selfVar, progVars.paramVars,
//	        progVars.resultVar, progVars.excVar, progVars.heapAtPreVar, progVars.savedHeapAtPreVar,
//	        INVALID_ID, toBeSaved);
//    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    
    protected Map<ProgramVariable, ProgramVariable> getReplaceMap(
	    		      ProgramVariable selfVar, 
	    		      ImmutableList<ProgramVariable> paramVars, 
	    		      ProgramVariable resultVar, 
	    		      ProgramVariable excVar,
	    		      Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    		      Services services) {
	final Map<ProgramVariable, ProgramVariable> result = new LinkedHashMap<ProgramVariable, ProgramVariable>();
	
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

        if(atPreVars != null) {
          final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
          for(LocationVariable h : heapLDT.getAllHeaps()) {
             if(atPreVars.get(h) != null) {
                assert originalAtPreVars.get(h).sort().equals(atPreVars.get(h).sort());
                result.put(originalAtPreVars.get(h), atPreVars.get(h));
             }
          }        
        }

	return result;
    }
    
    
    protected Map<Term, Term> getReplaceMap(
	    		      LocationVariable baseHeap,
	    		      Term heapTerm,
	    		      Term selfTerm, 
	    		      ImmutableList<Term> paramTerms, 
	    		      Term resultTerm, 
	    		      Term excTerm,
                              Map<LocationVariable,Term> atPres,
	    		      Services services) {
	final Map<Term,Term> result = new LinkedHashMap<Term,Term>();
	
	//heap
	assert heapTerm != null;
	assert heapTerm.sort().equals(services.getTypeConverter()
		                              .getHeapLDT()
		                              .targetSort());
	result.put(baseHeap != null ? TB.var(baseHeap) : TB.getBaseHeap(services), heapTerm);
	
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

        if(atPres != null) {
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            for(LocationVariable h : heapLDT.getAllHeaps()) {
            if(atPres.get(h) != null) {
              assert originalAtPreVars.get(h).sort().equals(atPres.get(h).sort());
	      result.put(TB.var(originalAtPreVars.get(h)), atPres.get(h));
            }
          }
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
    public IProgramMethod getTarget() {
        return pm;
    }
    
    
    @Override
    public boolean hasMby() {
	return originalMby != null;
    }
    
        
    @Override
    public Term getPre(LocationVariable heap,
                       ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable,? extends ProgramVariable> atPreVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar, 
                                             paramVars, 
                                             null, 
                                             null,
                                             atPreVars, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPres.get(heap));
    }

    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable,? extends ProgramVariable> atPreVars,
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
	final Map<Term, Term> replaceMap = getReplaceMap(heap, heapTerm, 
					     selfTerm, 
					     paramTerms, 
					     null, 
					     null,
                                             atPres, 
					     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPres.get(heap));
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
          if(p == null) {
            assert heap == services.getTypeConverter().getHeapLDT().getSavedHeap() && !hasModifiesClause();
            continue;
          }
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
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar, 
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
	final Map<Term, Term> replaceMap = getReplaceMap(null, heapTerm, 
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
    public String getPlainText(Services services) {
       return getText(false, services);
    }
    
    @Override
    public String getHTMLText(Services services) {
       return getText(true, services);
    }
    
   private String getText(boolean includeHtmlMarkup, Services services) {
      final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
      final LocationVariable baseHeap = heapLDT.getHeap();
      final StringBuffer sig = new StringBuffer();
      if (originalResultVar != null) {
         sig.append(originalResultVar);
         sig.append(" = ");
      }
      else if (pm.isConstructor()) {
         sig.append(originalSelfVar);
         sig.append(" = new ");
      }
      if (!pm.isStatic() && !pm.isConstructor()) {
         sig.append(originalSelfVar);
         sig.append(".");
      }
      sig.append(pm.getName());
      sig.append("(");
      for (ProgramVariable pv : originalParamVars) {
         sig.append(pv.name()).append(", ");
      }
      if (!originalParamVars.isEmpty()) {
         sig.setLength(sig.length() - 2);
      }
      sig.append(")");
      sig.append(" catch(");
      sig.append(originalExcVar);
      sig.append(")");

      final String mby = hasMby() ? LogicPrinter.quickPrintTerm(originalMby, services) : null;

      String mods = "";
      for (LocationVariable h : heapLDT.getAllHeaps()) {
         if (originalMods.get(h) != null) {
            String printMods = LogicPrinter.quickPrintTerm(originalMods.get(h), services);
            mods = mods
                  + (includeHtmlMarkup ? "<br><b>" : "\n")
                  + "mod"
                  + (h == baseHeap ? "" : "[" + h + "]")
                  + (includeHtmlMarkup ? "</b> " : ": ")
                  + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printMods, false) : printMods.trim());
            if (h == baseHeap && !hasRealModifiesClause) {
               mods = mods + 
                      (includeHtmlMarkup ? "<b>" : "") +
               		 ", creates no new objects" +
               		 (includeHtmlMarkup ? "</b>" : "");
            }
         }
      }

      String pres = "";
      for (LocationVariable h : heapLDT.getAllHeaps()) {
         if (originalPres.get(h) != null) {
            String printPres = LogicPrinter.quickPrintTerm(originalPres.get(h), services);
            pres = pres
                  + (includeHtmlMarkup ? "<br><b>" : "\n")
                  + "pre"
                  + (h == baseHeap ? "" : "[" + h + "]")
                  + (includeHtmlMarkup ? "</b> " : ": ")
                  + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPres, false) : printPres.trim());
         }
      }

      String posts = "";
      for (LocationVariable h : heapLDT.getAllHeaps()) {
         if (originalPres.get(h) != null) {
            String printPosts = LogicPrinter.quickPrintTerm(originalPosts.get(h), services);
            posts = posts
                  + (includeHtmlMarkup ? "<br><b>" : "\n")
                  + "post"
                  + (h == baseHeap ? "" : "[" + h + "]")
                  + (includeHtmlMarkup ? "</b> " : ": ")
                  + (includeHtmlMarkup ? LogicPrinter.escapeHTML(printPosts, false) : printPosts.trim());
         }
      }

      if (includeHtmlMarkup) {
         return "<html>"
               + "<i>"
               + LogicPrinter.escapeHTML(sig.toString(), false)
               + "</i>"
               + pres
               + posts
               + mods
               + (hasMby() ? "<br><b>measured-by</b> "+ LogicPrinter.escapeHTML(mby, false) : "")
               + "<br><b>termination</b> "
               + getModality()
               + (transactionApplicableContract() ? "<br><b>transaction applicable</b>" : "") + 
               "</html>";
         
      }
      else {
         return sig.toString()
               + pres
               + posts
               + mods
               + (hasMby() ? "\nmeasured-by: "+ mby : "")
               + "\ntermination: "
               + getModality()
               + (transactionApplicableContract() ? "\ntransaction applicable:" : "");
      }
   }
    
    
    @Override
    public boolean toBeSaved() {
	return toBeSaved;
    }
    
    
    @Override
    public String proofToString(Services services) {
	assert toBeSaved;
	final StringBuffer sb = new StringBuffer();
    final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
    final LocationVariable baseHeap = heapLDT.getHeap();
	sb.append(baseName).append(" {\n");
	
	//print var decls
	sb.append("  \\programVariables {\n");
	if(originalSelfVar != null) {
	    sb.append("    ").append(originalSelfVar.proofToString());
	}
	for(ProgramVariable originalParamVar : originalParamVars) {
	    sb.append("    ").append(originalParamVar.proofToString());
	}
	if(originalResultVar != null) {
	    sb.append("    ").append(originalResultVar.proofToString());
	}
	sb.append("    ").append(originalExcVar.proofToString());
	sb.append("    ").append(originalAtPreVars.get(baseHeap).proofToString());	
	sb.append("  }\n");

	//prepare Java program
	final Expression[] args 
		= new ProgramVariable[originalParamVars.size()];
	int i = 0;
	for(ProgramVariable arg : originalParamVars) {
	    args[i++] = arg;
	}
	final MethodReference mr 
		= new MethodReference(new ImmutableArray<Expression>(args), 
			              pm.getProgramElementName(), 
			              originalSelfVar);
	final Statement callStatement;
	if(originalResultVar == null) {
	    callStatement = mr;
	} else {
	    callStatement = new CopyAssignment(originalResultVar, mr);
	}
	final CatchAllStatement cas 
		= new CatchAllStatement(new StatementBlock(callStatement), 
					(LocationVariable)originalExcVar);
	final StatementBlock sblock = new StatementBlock(cas);
	final JavaBlock jb = JavaBlock.createJavaBlock(sblock);
	
	//print contract term
	final Term update 
		= TB.tf().createTerm(
			ElementaryUpdate.getInstance(originalAtPreVars.get(baseHeap)),
			TB.getBaseHeap(services));	
	final Term modalityTerm 
		= TB.tf().createTerm(modality, 
				     new Term[]{originalPosts.get(baseHeap)}, 
				     new ImmutableArray<QuantifiableVariable>(),
				     jb);
	final Term updateTerm
		= TB.tf().createTerm(UpdateApplication.UPDATE_APPLICATION, 
				     update, 
				     modalityTerm);
	final Term contractTerm 
		= TB.tf().createTerm(Junctor.IMP, originalPres.get(baseHeap), updateTerm);
	final LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), 
            			   	       	 new NotationInfo(), 
            			   	       	 null);
	try {
	    lp.printTerm(contractTerm);
	} catch(IOException e) {
	    throw new RuntimeException(e);
	}
	sb.append(lp.toString());
	
	//print modifies
	lp.reset();
	try {
	    lp.printTerm(originalMods.get(baseHeap));
	} catch(IOException e) {
	    throw new RuntimeException(e);
	}
	sb.append("  \\modifies ").append(lp.toString());
	
	sb.append("};\n");
	return sb.toString();
    }
    
    
    @Override
    public Modality getModality() {
        return modality;
    }
    
    @Override
    public Term getPost(LocationVariable heap,
                        ProgramVariable selfVar, 
                        ImmutableList<ProgramVariable> paramVars, 
                        ProgramVariable resultVar, 
                        ProgramVariable excVar,
                        Map<LocationVariable,? extends ProgramVariable> atPreVars,
                        Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert excVar != null;
        assert atPreVars.size() != 0;
        assert services != null;
	final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar, 
                                       	     paramVars, 
                                       	     resultVar, 
                                       	     excVar, 
                                       	     atPreVars,
                                       	     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPosts.get(heap));
    }

    public Term getPost(List<LocationVariable> heapContext,
                        ProgramVariable selfVar, 
                        ImmutableList<ProgramVariable> paramVars, 
                        ProgramVariable resultVar, 
                        ProgramVariable excVar,
                        Map<LocationVariable,? extends ProgramVariable> atPreVars,
                        Services services) {
       Term result = null;
       for(LocationVariable heap : heapContext) {
          final Term p = getPost(heap, selfVar, paramVars, resultVar, excVar, atPreVars, services);
          if(result == null) {
            result = p;
          }else{
            result = TB.and(result, p);
          }
       }
       return result;

    }    
    
    @Override
    public Term getPost(LocationVariable heap,
                        Term heapTerm,
	                Term selfTerm, 
                        ImmutableList<Term> paramTerms, 
                        Term resultTerm, 
                        Term excTerm,
                        Map<LocationVariable,Term> atPres,
                        Services services) {
	assert heapTerm != null;
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert (resultTerm == null) == (originalResultVar == null);
        assert excTerm != null;
        assert atPres.size() != 0;
        assert services != null;
	final Map<Term, Term> replaceMap = getReplaceMap(heap, heapTerm,
		                             selfTerm, 
                                             paramTerms, 
                                             resultTerm, 
                                             excTerm, 
                                       	     atPres,
                                       	     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPosts.get(heap));
    }    

    public Term getPost(List<LocationVariable> heapContext,
                        Map<LocationVariable,Term> heapTerms,
	                Term selfTerm, 
                        ImmutableList<Term> paramTerms, 
                        Term resultTerm, 
                        Term excTerm,
                        Map<LocationVariable,Term> atPres,
                        Services services) {
       Term result = null;
       for(LocationVariable heap : heapContext) {
          final Term p = getPost(heap, heapTerms.get(heap), selfTerm, paramTerms, resultTerm, excTerm, atPres, services);
          if(p == null) {
            assert heap == services.getTypeConverter().getHeapLDT().getSavedHeap() && !hasModifiesClause();
            continue;
          }
          if(result == null) {
            result = p;
          }else{
            result = TB.and(result, p);
          }
       }
       return result;
    }

    public boolean isReadOnlyContract(Services services) {
        return originalMods.get(services.getTypeConverter().getHeapLDT().getHeap()).op() == 
                services.getTypeConverter().getLocSetLDT().getEmpty();
    }
    
    public Term getAnyMod(Term mod, ProgramVariable selfVar, 
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert services != null;
	final Map<ProgramVariable, ProgramVariable> replaceMap = getReplaceMap(selfVar, 
                                             paramVars, 
                                             null, 
                                             null,
                                             null,
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(mod);
    }

    @Override
    public Term getMod(LocationVariable heap, ProgramVariable selfVar, 
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
       return getAnyMod(this.originalMods.get(heap), selfVar, paramVars, services);
    }

    private Term getAnyMod(LocationVariable heap, Term mod, Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
	assert heapTerm != null;	
        assert (selfTerm == null) == (originalSelfVar == null);
        assert paramTerms != null;
        assert paramTerms.size() == originalParamVars.size();
        assert services != null;
	final Map<Term, Term> replaceMap = getReplaceMap(heap, heapTerm,
		                             selfTerm, 
                                             paramTerms, 
                                             null, 
                                             null,
                                             null, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(mod);
    }
    
    @Override
    public boolean hasModifiesClause() {
        return this.hasRealModifiesClause;
    }
  
    @Override    
    public Term getMod(LocationVariable heap, Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
        return getAnyMod(heap, this.originalMods.get(heap), heapTerm, selfTerm, paramTerms, services);
    }    
    
    @Override
    public String toString() {
	return "pre: " 
		+ originalPres
		+ "; mby: " 
		+ originalMby
		+ "; post: " 
		+ originalPosts 
		+ "; mods: " 
		+ originalMods
		+ "; hasMod: "
		+ hasRealModifiesClause
		+ "; termination: "
		+ getModality()
                + "; transaction: "
		+ transactionApplicableContract();
    }


    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
	    Contract contract) {
	return new FunctionalOperationContractPO(initConfig,
	        (FunctionalOperationContract) contract);
    }

	        	        
    @Override
    public String getDisplayName() {
        return ContractFactory.generateDisplayName(baseName, kjt, pm, specifiedIn, id);
    }


    @Override
    public VisibilityModifier getVisibility() {
	assert false; // this is currently not applicable for contracts
	return null;
    }

    public boolean transactionApplicableContract() {
        return transaction;
    }

    @Override
    public FunctionalOperationContract setID(int newId) {
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   kjt,
                                                   pm,
                                                   specifiedIn,
                                                   modality,
                                                   originalPres,
                                                   originalMby,
                                                   originalPosts,
                                                   originalMods,
                                                   hasRealModifiesClause,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalAtPreVars,
                                                   newId,
                                                   toBeSaved,
                                                   transaction);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
                              IObserverFunction newPM) {
        assert newPM instanceof IProgramMethod;
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   newKJT,
                                                   (IProgramMethod) newPM,
                                                   specifiedIn,
                                                   modality,
                                                   originalPres,
                                                   originalMby,
                                                   originalPosts,
                                                   originalMods,
                                                   hasRealModifiesClause,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalAtPreVars,
                                                   id,
                                                   toBeSaved && newKJT.equals(
                kjt), transaction);
    }
    
    
    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName(baseName, kjt, pm, specifiedIn);
    }

}

