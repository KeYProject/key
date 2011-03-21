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

import java.io.IOException;
import java.util.HashMap;
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
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
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
    private final LocationVariable originalHeapAtPreVar;
    private final int id;
    private final boolean toBeSaved;
    
    
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
                                  LocationVariable heapAtPreVar,
                                  int id,
                                  boolean toBeSaved) {
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
	this.originalSelfVar        = selfVar;
	this.originalParamVars      = paramVars;
	this.originalResultVar      = resultVar;
	this.originalExcVar         = excVar;
	this.originalHeapAtPreVar   = heapAtPreVar;
	this.id                     = id;	
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
                                 LocationVariable heapAtPreVar,
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
             selfVar,
             paramVars,
             resultVar,
             excVar,
             heapAtPreVar,
             INVALID_ID,
             toBeSaved);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private static Term atPreify(Term t, 
	    			 ProgramVariable heapAtPreVar,
	    			 Services services) {
	final Map<Term,Term> map = new HashMap<Term,Term>();
	map.put(TB.heap(services), TB.var(heapAtPreVar));
        return new OpReplacer(map).replace(t);
    }

    
    private Map /*Operator, Operator, Term -> Term*/ getReplaceMap(
	    		      ProgramVariable selfVar, 
	    		      ImmutableList<ProgramVariable> paramVars, 
	    		      ProgramVariable resultVar, 
	    		      ProgramVariable excVar,
	    		      ProgramVariable heapAtPreVar,
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
	    assert originalHeapAtPreVar.sort().equals(heapAtPre.sort());
	    result.put(TB.var(originalHeapAtPreVar), heapAtPre);
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
                			 originalHeapAtPreVar,
                			 newId,
                			 toBeSaved);	
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
                			 originalHeapAtPreVar,
                			 id,
                			 toBeSaved && newKJT.equals(kjt));	
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
    public Term getPost(ProgramVariable selfVar, 
                        ImmutableList<ProgramVariable> paramVars, 
                        ProgramVariable resultVar, 
                        ProgramVariable excVar,
                        ProgramVariable heapAtPreVar,
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
        Term post = TB.imp(atPreify(originalPre, 
        			    originalHeapAtPreVar,
        			    services), 
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
        	    			   originalHeapAtPreVar, 
        	    			   services);
            Term otherMod = other.getMod(originalSelfVar, 
                                         originalParamVars, 
                                         services);

            pre = TB.or(pre, otherPre);
            mby = mby != null && otherMby != null
                  ? TB.ife(otherPre, otherMby, mby)
                  : null;            
            post = TB.and(post, TB.imp(atPreify(otherPre, 
        	    				originalHeapAtPreVar, 
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
                                         originalHeapAtPreVar,
                                         INVALID_ID,
                                         toBeSaved);
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
		 			 originalHeapAtPreVar,
		 			 id,
		 			 toBeSaved);
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
