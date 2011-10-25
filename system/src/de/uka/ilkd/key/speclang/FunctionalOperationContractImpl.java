// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;


/**
 * Standard implementation of the OperationContract interface.
 */
public final class FunctionalOperationContractImpl implements FunctionalOperationContract {
    
    protected static final TermBuilder TB = TermBuilder.DF;

    final String baseName;
    final String name;
    final KeYJavaType kjt;    
    final ProgramMethod pm;
    final Modality modality;
    final Modality poModality;
    final Term originalPre;
    final Term originalMby;    
    final Term originalPost;
    final Term originalMod;
    final Term originalModBackup;
    final ProgramVariable originalSelfVar;
    final ImmutableList<ProgramVariable> originalParamVars;
    final ProgramVariable originalResultVar;
    final ProgramVariable originalExcVar;
    final LocationVariable originalHeapAtPreVar;
    final LocationVariable originalSavedHeapAtPreVar;
    final int id;
    final boolean transaction;
    final boolean toBeSaved;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    FunctionalOperationContractImpl(String baseName,
	                          String name,
                                  KeYJavaType kjt,	                          
                                  ProgramMethod pm,
            		          Modality modality,
            		          Term pre,
            		          Term mby,
            		          Term post,
            		          Term mod,
                                  Term modBackup,
            		          ProgramVariable selfVar,
            		          ImmutableList<ProgramVariable> paramVars,
            		          ProgramVariable resultVar,
            		          ProgramVariable excVar,
                                  LocationVariable heapAtPreVar,
                                  LocationVariable savedHeapAtPreVar,
                                  int id,
                                  boolean toBeSaved) {
	assert !(name == null && baseName == null);
        assert kjt != null;	
        assert pm != null;
        assert pre != null;
        assert post != null;
        assert modality != null;
        assert (selfVar == null) == pm.isStatic();
        assert paramVars != null;
        assert paramVars.size() == pm.getParameterDeclarationCount();
        assert (resultVar == null) == (pm.getKeYJavaType() == null);
        assert excVar != null;
        assert heapAtPreVar != null;
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
	this.originalModBackup      = modBackup;
	this.originalSelfVar        = selfVar;
	this.originalParamVars      = paramVars;
	this.originalResultVar      = resultVar;
	this.originalExcVar         = excVar;
	this.originalHeapAtPreVar   = heapAtPreVar;
	this.originalSavedHeapAtPreVar = savedHeapAtPreVar;
	this.id                     = id;
        this.transaction            = (modBackup != null);
        this.poModality             = (modality == Modality.DIA_TRANSACTION ? 
                                          Modality.DIA : 
                                          (modality == Modality.BOX_TRANSACTION ? Modality.BOX : modality));	
	this.toBeSaved	            = toBeSaved;
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
     * @param heapAtPreVar the variable used for the pre-heap
     */
    FunctionalOperationContractImpl(String baseName,
                                 KeYJavaType kjt,	    
                                 ProgramMethod pm,
            		         Modality modality,
            		         Term pre,
            		         Term mby,            		         
            		         Term post,
            		         Term mod,
                                 Term modBackup,
            		         ProgramVariable selfVar,
            		         ImmutableList<ProgramVariable> paramVars,
            		         ProgramVariable resultVar,
            		         ProgramVariable excVar,
                                 LocationVariable heapAtPreVar,
                                 LocationVariable savedHeapAtPreVar,
                                 boolean toBeSaved) {
        this(baseName,
             null,
             kjt,             
             pm,
             modality,
             pre,
             mby,
             post,
             mod,
             modBackup,
             selfVar,
             paramVars,
             resultVar,
             excVar,
             heapAtPreVar,
             savedHeapAtPreVar,
             INVALID_ID,
             toBeSaved);
    }
    
    
    /**
     * Creates an operation contract.
     * 
     * @param baseName base name of the contract (does not have to be unique)
     * @param pm 	the ProgramMethod to which the contract belongs
     * @param modality the modality of the contract
     * @param pre 	the precondition of the contract
     * @param mby 	the measured_by clause of the contract 
     * @param post 	the postcondition of the contract
     * @param mod 	the modifies clause of the contract
     * @param progVars collection of variables for the receiver object,
     * 			operation parameters, operation result, thrown exception
     * 			and the pre-heap
     */
    FunctionalOperationContractImpl(String baseName, ProgramMethod pm,
	    Modality modality, Term pre, Term mby, Term post, Term mod, Term modBackup,
	    ProgramVariableCollection progVars, boolean toBeSaved) {
	this(baseName, null, pm.getContainerType(), pm, modality, pre, mby,
	        post, mod, modBackup, progVars.selfVar, progVars.paramVars,
	        progVars.resultVar, progVars.excVar, progVars.heapAtPreVar, progVars.savedHeapAtPreVar,
	        INVALID_ID, toBeSaved);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    
    private Map /*Operator, Operator, Term -> Term*/ getReplaceMap(
	    		      ProgramVariable selfVar, 
	    		      ImmutableList<ProgramVariable> paramVars, 
	    		      ProgramVariable resultVar, 
	    		      ProgramVariable excVar,
	    		      ProgramVariable heapAtPreVar,
	    		      ProgramVariable savedHeapAtPreVar,
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
	if(heapAtPreVar != null) {
	    assert originalHeapAtPreVar.sort().equals(heapAtPreVar.sort());
	    result.put(originalHeapAtPreVar, heapAtPreVar);
	}

        //savedAtPre-functions
	if(savedHeapAtPreVar != null) {
	    assert originalSavedHeapAtPreVar.sort().equals(savedHeapAtPreVar.sort());
	    result.put(originalSavedHeapAtPreVar, savedHeapAtPreVar);
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
	    		      Term savedHeapAtPre,
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
	    assert originalHeapAtPreVar.sort().equals(heapAtPre.sort());
	    result.put(TB.var(originalHeapAtPreVar), heapAtPre);
	}

        //savedAtPre-functions
	if(savedHeapAtPre != null) {
	    assert originalSavedHeapAtPreVar.sort().equals(savedHeapAtPre.sort());
	    result.put(TB.var(originalSavedHeapAtPreVar), savedHeapAtPre);
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
                       ProgramVariable savedHeapAtPreVar,
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
                                             savedHeapAtPreVar, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPre);
    }
    
    
    @Override
    public Term getPre(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Term savedHeapAtPre,
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
                                             savedHeapAtPre, 
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
                                             null,
					     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalMby);
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
	    sig.append(pv.name()).append(", ");
	}
	if(!originalParamVars.isEmpty()) {
	    sig.setLength(sig.length() - 2);
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
        final String modBackup = originalModBackup != null ? LogicPrinter.quickPrintTerm(originalModBackup, services) : null;
                      
        return "<html>"
                + "<i>" + LogicPrinter.escapeHTML(sig.toString(), false) + "</i>"
                + "<br><b>pre</b> "
                + LogicPrinter.escapeHTML(pre, false)
                + "<br><b>post</b> "
                + LogicPrinter.escapeHTML(post, false)
                + "<br><b>mod</b> "
                + LogicPrinter.escapeHTML(mod, false)
                + (modBackup != null ? "<br><b>mod_backup</b> "+ LogicPrinter.escapeHTML(modBackup, false) : "")
                + (hasMby() 
                   ? "<br><b>measured-by</b> " + LogicPrinter.escapeHTML(mby, 
                	   						 false)
                   : "")                
                + "<br><b>termination</b> "
                + getModality()
                + "</html>";
    }    
    
    
    @Override
    public boolean toBeSaved() {
	return toBeSaved;
    }
    
    
    @Override
    public String proofToString(Services services) {
	assert toBeSaved;
	final StringBuffer sb = new StringBuffer();
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
	sb.append("    ").append(originalHeapAtPreVar.proofToString());	
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
			ElementaryUpdate.getInstance(originalHeapAtPreVar),
			TB.heap(services));	
	final Term modalityTerm 
		= TB.tf().createTerm(modality, 
				     new Term[]{originalPost}, 
				     new ImmutableArray<QuantifiableVariable>(),
				     jb);
	final Term updateTerm
		= TB.tf().createTerm(UpdateApplication.UPDATE_APPLICATION, 
				     update, 
				     modalityTerm);
	final Term contractTerm 
		= TB.tf().createTerm(Junctor.IMP, originalPre, updateTerm);
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
	    lp.printTerm(originalMod);
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
    public Modality getPOModality() {
        return poModality;
    }

  
    @Override
    public Term getPost(ProgramVariable selfVar, 
                        ImmutableList<ProgramVariable> paramVars, 
                        ProgramVariable resultVar, 
                        ProgramVariable excVar,
                        ProgramVariable heapAtPreVar,
                        ProgramVariable savedHeapAtPreVar,
                        Services services) {
        assert (selfVar == null) == (originalSelfVar == null);
        assert paramVars != null;
        assert paramVars.size() == originalParamVars.size();
        assert (resultVar == null) == (originalResultVar == null);
        assert excVar != null;
        assert heapAtPreVar != null;
        assert services != null;
	final Map replaceMap = getReplaceMap(selfVar, 
                                       	     paramVars, 
                                       	     resultVar, 
                                       	     excVar, 
                                       	     heapAtPreVar,
                                             savedHeapAtPreVar, 
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
                        Term savedHeapAtPre,
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
                                             savedHeapAtPre, 
                                       	     services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(originalPost);
    }    

    public Term getAnyMod(Term mod, ProgramVariable selfVar, 
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
                                             null,
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
        return or.replace(mod);
    }

    @Override
    public Term getMod(ProgramVariable selfVar, 
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
       return getAnyMod(this.originalMod, selfVar, paramVars, services);
    }

    @Override
    public Term getBackupMod(ProgramVariable selfVar, 
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) {
       return getAnyMod(this.originalModBackup, selfVar, paramVars, services);
    }

    private Term getAnyMod(Term mod, Term heapTerm,
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
                                             null, 
                                             services);
	final OpReplacer or = new OpReplacer(replaceMap);
	return or.replace(mod);
    }
  
    @Override    
    public Term getMod(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
        return getAnyMod(this.originalMod, heapTerm, selfTerm, paramTerms, services);
    }    

    @Override    
    public Term getBackupMod(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services) {
        return getAnyMod(this.originalModBackup, heapTerm, selfTerm, paramTerms, services);
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
                + (originalModBackup != null ? "; mod_backup: " + originalModBackup : "")
		+ "; termination: "
		+ getModality();
    }


    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
	    Contract contract) {
	return new FunctionalOperationContractPO(initConfig,
	        (FunctionalOperationContract) contract);
    }

	        	        
    @Override
    public String getDisplayName() {
	return getName();
    }


    @Override
    public VisibilityModifier getVisibility() {
	assert false; // this is currently not applicable for contracts
	return null;
    }

    public boolean transactionContract() {
        return transaction;
    } 

    @Override
    public FunctionalOperationContract setID(int newId) {
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   kjt,
                                                   pm,
                                                   modality,
                                                   originalPre,
                                                   originalMby,
                                                   originalPost,
                                                   originalMod,
                                                   originalModBackup,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalHeapAtPreVar,
                                                   originalSavedHeapAtPreVar,
                                                   newId,
                                                   toBeSaved);
    }


    @Override
    public Contract setTarget(KeYJavaType newKJT,
                              ObserverFunction newPM) {
        assert newPM instanceof ProgramMethod;
        return new FunctionalOperationContractImpl(baseName,
                                                   null,
                                                   newKJT,
                                                   (ProgramMethod) newPM,
                                                   modality,
                                                   originalPre,
                                                   originalMby,
                                                   originalPost,
                                                   originalMod,
                                                   originalModBackup,
                                                   originalSelfVar,
                                                   originalParamVars,
                                                   originalResultVar,
                                                   originalExcVar,
                                                   originalHeapAtPreVar,
                                                   originalSavedHeapAtPreVar,
                                                   id,
                                                   toBeSaved && newKJT.equals(
                kjt));
    }
}
