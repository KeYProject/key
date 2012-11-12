// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodOrConstructorReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSinppetFactory;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class UseOperationContractRule implements BuiltInRule {
    
    public static final UseOperationContractRule INSTANCE 
                                            = new UseOperationContractRule();    

    private static final Name NAME = new Name("Use Operation Contract");
    private static final TermBuilder TB = TermBuilder.DF;
    
    private Term lastFocusTerm;
    private Instantiation lastInstantiation;   
    

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private UseOperationContractRule() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private static Pair<Expression,MethodOrConstructorReference> getMethodCall(
	    						JavaBlock jb,
	    				                Services services) {
	final Expression actualResult;
        final MethodOrConstructorReference mr;
        
        final SourceElement activeStatement = JavaTools.getActiveStatement(jb);
        //active statement must be method reference or assignment with
        //method reference
        if(activeStatement instanceof MethodReference) {
            actualResult = null;
            mr = (MethodReference) activeStatement;
        } else if(activeStatement instanceof New 
        	  && ((New)activeStatement).getTypeDeclarationCount() == 0) {
            actualResult = null;
            mr = (New) activeStatement;
        } else if(activeStatement instanceof CopyAssignment) {
            final CopyAssignment ca = (CopyAssignment) activeStatement;
            final Expression lhs = ca.getExpressionAt(0);
            final Expression rhs = ca.getExpressionAt(1);
            if((rhs instanceof MethodReference 
        	|| rhs instanceof New 
        	   && ((New)rhs).getTypeDeclarationCount() == 0)
               && (lhs instanceof LocationVariable 
                   || lhs instanceof FieldReference)) {
        	actualResult = lhs;
        	mr = (MethodOrConstructorReference) rhs;
            } else {
        	return null;
            }
        } else {
            return null;
        }
        
        //constructor may not refer to anonymous class
        if(mr instanceof New 
           && ((New)mr).getTypeReference().getKeYJavaType().getJavaType() 
                       instanceof ClassDeclaration
           && ((ClassDeclaration)((New)mr).getTypeReference()
        	                          .getKeYJavaType()
        	                          .getJavaType()).isAnonymousClass()) {
            return null;
        }

        //receiver must be simple
        final ReferencePrefix rp = mr.getReferencePrefix();
        if(rp != null 
           && !ProgramSVSort.SIMPLEEXPRESSION.canStandFor(rp, null, services)
           && !(rp instanceof ThisReference)
           && !(rp instanceof SuperReference)
           && !(rp instanceof TypeReference)) {
            return null;
        } else {
            return new Pair<Expression,MethodOrConstructorReference>(
        	    				actualResult, 
        	    				mr);
        }
    }
    
    
    private static KeYJavaType getStaticPrefixType(
	    				MethodOrConstructorReference mr,
	                                Services services,
	                                ExecutionContext ec) {
	if(mr instanceof MethodReference) { 
	    return ((MethodReference)mr).determineStaticPrefixType(services, 
		                         ec);
	} else {
	    New n = (New) mr;
	    return n.getKeYJavaType(services, ec);
	}
    }
    
    
    private static IProgramMethod getProgramMethod(
            MethodOrConstructorReference mr,
            KeYJavaType staticType, 
            ExecutionContext ec,
            Services services) {
        IProgramMethod result;	
        if(mr instanceof MethodReference) { //from MethodCall.java
            MethodReference methRef = (MethodReference) mr;
            if(ec != null) {
                result = methRef.method(services, staticType, ec);
                if(result == null) {
                    // if a method is declared protected and prefix and
                    // execContext are in different packages we have to
                    // simulate visibility rules like being in prefixType
                    result = methRef.method(services, 
                            staticType, 
                            methRef.getMethodSignature(services, ec), 
                            staticType);
                }
            } else {
                result = methRef.method(services, 
                        staticType, 
                        methRef.getMethodSignature(services, ec), 
                        staticType);
            }
        } else {
            New n = (New) mr;
            ImmutableList<KeYJavaType> sig = ImmutableSLList.<KeYJavaType>nil();
            for(Expression e : n.getArguments()) {
                sig = sig.append(e.getKeYJavaType(services, ec));
            }
            result = services.getJavaInfo().getConstructor(staticType, sig);
            assert result != null;
        }
        return result;
    }
    
    
    private static Term getActualSelf(MethodOrConstructorReference mr,
	    		              IProgramMethod pm,
	    		              ExecutionContext ec, 
	    		              Services services) {
	final TypeConverter tc = services.getTypeConverter();
	final ReferencePrefix rp = mr.getReferencePrefix();
	if(pm.isStatic() || pm.isConstructor()) {
	    return null;
	} else if(rp == null 
		  || rp instanceof ThisReference 
		  || rp instanceof SuperReference) {
	    return tc.findThisForSort(pm.getContainerType().getSort(), ec);
	} else if(rp instanceof FieldReference
		  && ((FieldReference) rp).referencesOwnInstanceField()) {
	    final ReferencePrefix rp2 
	    	= ((FieldReference)rp).setReferencePrefix(
	    					ec.getRuntimeInstance());
	    return tc.convertToLogicElement(rp2);
	} else {
	    return tc.convertToLogicElement(rp, ec);
	}
    }
    
    
    private static ImmutableList<Term> getActualParams(
	    					MethodOrConstructorReference mr,
	    					ExecutionContext ec,
	    					Services services) {        
	ImmutableList<Term> result = ImmutableSLList.<Term>nil();
	for(Expression expr : mr.getArguments()) {
	    Term actualParam 
	    	= services.getTypeConverter().convertToLogicElement(expr, ec);
	    result = result.append(actualParam);
	}
	return result;
    }
    
    
	public static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
            Instantiation inst, Services services) {
    	
		if(inst == null) {
    		return DefaultImmutableSet.
    				<FunctionalOperationContract>nil();
    	}

    	//there must be applicable contracts for the operation
    	return getApplicableContracts(services, inst.pm, inst.staticType, inst.mod);

    }
       
    /**
     * Returns the operation contracts which are applicable for the passed 
     * operation and the passed modality
     */
    private static ImmutableSet<FunctionalOperationContract> getApplicableContracts(
	    						  						  Services services, 
                                                          IProgramMethod pm, 
                                                          KeYJavaType kjt,
                                                          Modality modality) {
        ImmutableSet<FunctionalOperationContract> result 
                = services.getSpecificationRepository()
                          .getOperationContracts(kjt, pm, modality);
        
        //in box modalities, diamond contracts may be applied as well
        if(modality == Modality.BOX) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(kjt, 
                                        	  		 pm,
                                        	  		 Modality.DIA));
        }else if(modality == Modality.BOX_TRANSACTION) {
            result = result.union(services.getSpecificationRepository()
                                          .getOperationContracts(kjt, 
                                        	  		 pm,
                                        	  		 Modality.DIA_TRANSACTION));
        }

        return result;
    }

    
    
    /**
     * @return (assumption, anon update, anon heap)
     */
    private static AnonUpdateData createAnonUpdate(LocationVariable heap, IProgramMethod pm, 
	                                     	    	   Term mod, 
	                                     	    	   Services services) {
	assert pm != null;
	assert mod != null;
	
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name methodHeapName = new Name(TB.newName(services, heap+"After_" + pm.getName()));
	final Function methodHeapFunc = new Function(methodHeapName, heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(methodHeapFunc);
    final Term methodHeap = TB.func(methodHeapFunc);
	final Name anonHeapName = new Name(TB.newName(services, "anon_" + heap + "_" + pm.getName()));
	final Function anonHeapFunc = new Function(anonHeapName, heap.sort(), true);
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeap = TB.func(anonHeapFunc);	
	final Term assumption = TB.equals(TB.anon(services, 
				          TB.var(heap), 
				          mod,
				          anonHeap),
                            methodHeap); 
	final Term anonUpdate = TB.elementary(services, heap, methodHeap);
	
	return new AnonUpdateData(assumption, anonUpdate, methodHeap, TB.getBaseHeap(services), anonHeap);
    } 
    
    
    private static Term getFreePost(IProgramMethod pm,
	    		     	    KeYJavaType kjt,
	    		     	    Term resultTerm,
	    		     	    Term selfTerm,
	    		     	    Term heapAtPre,
	    		     	    Services services) {
        final Term result;
        if(pm.isConstructor()) {
            assert resultTerm == null;
            assert selfTerm != null;
            result = TB.and(new Term[]{
        	      TB.not(TB.equals(selfTerm, TB.NULL(services))),
                      OpReplacer.replace(TB.getBaseHeap(services), 
        	                  	 heapAtPre, 
        	                   	 TB.not(TB.created(services, 
        	                   	                   selfTerm))),
                      TB.created(services, selfTerm),
                      TB.exactInstance(services, kjt.getSort(), selfTerm)});            
        } else if(resultTerm != null) {
            result = TB.reachableValue(services, 
        	                       resultTerm, 
        	                       pm.getReturnType());
        } else {
            result = TB.tt();
        }
        return result;
    }
    
    
    private static PosInProgram getPosInProgram(JavaBlock jb) {
        ProgramElement pe = jb.program();        
   
        PosInProgram result = PosInProgram.TOP;
        
        if (pe instanceof ProgramPrefix) {
            ProgramPrefix curPrefix = (ProgramPrefix)pe;
       
            final ImmutableArray<ProgramPrefix> prefix 
            	= curPrefix.getPrefixElements();
            final int length = prefix.size();
                
            //fail fast check      
            curPrefix = prefix.get(length-1);//length -1 >= 0 as prefix array 
                                             //contains curPrefix as first element

            pe = curPrefix.getFirstActiveChildPos().getProgram(curPrefix);

            assert pe instanceof CopyAssignment 
                   || pe instanceof MethodReference
                   || pe instanceof New;
        
            int i = length - 1;
            do {
                result = curPrefix.getFirstActiveChildPos().append(result);
                i--;
                if (i >= 0) {
                    curPrefix = prefix.get(i);
                }
            } while(i >= 0);       

        } else {
            assert pe instanceof CopyAssignment 
                   || pe instanceof MethodReference
                   || pe instanceof New;
        }
        return result;
    }
    
    
    private static StatementBlock replaceStatement(JavaBlock jb, 
                                                   StatementBlock replacement) {
        PosInProgram pos = getPosInProgram(jb);
        int lastPos = pos.last();
        ContextStatementBlockInstantiation csbi = 
            new ContextStatementBlockInstantiation(pos, 
                                                   pos.up().down(lastPos+1), 
                                                   null, 
                                                   jb.program());
        final NonTerminalProgramElement result = 
            ProgramContextAdder.INSTANCE.start(
                        (JavaNonTerminalProgramElement)jb.program(), 
                        replacement, 
                        csbi);
        return (StatementBlock) result;
    }
        

    private Instantiation instantiate(Term focusTerm, Services services) {
	//result cached?
	if(focusTerm == lastFocusTerm) {
	    return lastInstantiation;
	}

	//compute
	final Instantiation result = computeInstantiation(focusTerm, services);
	
	//cache and return
	lastFocusTerm = focusTerm;
	lastInstantiation = result;
	return result;	
    }

    

    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    /**
     * Computes instantiation for contract rule on passed focus term.
     * Internally only serves as helper for instantiate(). 
     */
    public static Instantiation computeInstantiation(Term focusTerm, Services services) {
	//leading update?
	final Term u;
	final Term progPost;
	if(focusTerm.op() instanceof UpdateApplication) {
	    u = UpdateApplication.getUpdate(focusTerm);
	    progPost = UpdateApplication.getTarget(focusTerm);
	} else {
	    u = TB.skip();
	    progPost = focusTerm;
	}
	
	//focus (below update) must be modality term
	if(progPost.op() != Modality.BOX && progPost.op() != Modality.DIA && 
           progPost.op() != Modality.BOX_TRANSACTION && progPost.op() != Modality.DIA_TRANSACTION) {
	    return null;
	}
	final Modality mod = (Modality) progPost.op();

	//active statement must be method call or new
	final Pair<Expression,MethodOrConstructorReference> methodCall
	= getMethodCall(progPost.javaBlock(), services);
	if(methodCall == null) {
	    return null;
	}
	final Expression actualResult = methodCall.first;        
	final MethodOrConstructorReference mr = methodCall.second;        
    assert mr != null;
	//arguments of method call must be simple expressions
	final ExecutionContext ec 
	= JavaTools.getInnermostExecutionContext(progPost.javaBlock(), 
	        services); 	        
	for(Expression arg : mr.getArguments()) {
	    if(!ProgramSVSort.SIMPLEEXPRESSION
	            .canStandFor(arg, ec, services)) {
	        return null;
	    }
	}

	//collect further information
	final KeYJavaType staticType = getStaticPrefixType(mr, services, ec);
	assert staticType != null;
	final IProgramMethod pm = getProgramMethod(mr, 
	        staticType,
	        ec, 
	        services);
	assert pm != null : "Getting program method failed.\nReference: "+mr+", static type: "+staticType+", execution context: "+ec;
	final Term actualSelf = getActualSelf(mr, pm, ec, services);
	final ImmutableList<Term> actualParams  = getActualParams(mr, ec, services);

	//cache and return result
	final Instantiation result = new Instantiation(u, 
	        progPost, 
	        mod,
	        actualResult,
	        actualSelf,
	        staticType,
	        mr,
	        pm,
	        actualParams);
	return result;
    }
    
    
    @Override
    public boolean isApplicable(Goal goal, 
                                PosInOccurrence pio) {        
	//focus must be top level succedent
	if(pio == null || !pio.isTopLevel() || pio.isInAntec()) {
	    return false;
	}

	//instantiation must succeed
	final Instantiation inst = instantiate(pio.subTerm(), 
		                               goal.proof().getServices());
	if(inst == null) {
	    return false;
	}

        //there must be applicable contracts for the operation
        final ImmutableSet<FunctionalOperationContract> contracts 
                = getApplicableContracts(goal.proof().getServices(), 
                	                 inst.pm, 
                	                 inst.staticType, 
                	                 inst.mod);
        if(contracts.isEmpty()) {
            return false;
        }

        //applying a contract here must not create circular dependencies 
        //between proofs
        for(FunctionalOperationContract contract : contracts) {
            if(goal.proof().mgt().isContractApplicable(contract)) {
        	return true;
            }
        }
        return false;
    }

    
    @Override    
    public ImmutableList<Goal> apply(Goal goal, 
	    			     Services services, 
	    			     RuleApp ruleApp) {
	//get instantiation
	final Instantiation inst 
		= instantiate(ruleApp.posInOccurrence().subTerm(), services);
        final JavaBlock jb = inst.progPost.javaBlock();
        
        //configure contract
        final FunctionalOperationContract contract = 
        		(FunctionalOperationContract)((AbstractContractRuleApp) ruleApp)
                .getInstantiation(); 
        assert contract.getTarget().equals(inst.pm);

        Modality md = (Modality)TermBuilder.DF.goBelowUpdates(ruleApp.posInOccurrence().subTerm()).op();
        boolean transaction = (md == Modality.DIA_TRANSACTION || md == Modality.BOX_TRANSACTION); 
        final List<LocationVariable> heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);

	//prepare heapBefore_method

        Map<LocationVariable,LocationVariable> atPreVars = HeapContext.getBeforeAtPreVars(heapContext, services, "Before_"+inst.pm.getName());
        for(LocationVariable v : atPreVars.values()) {
     	  goal.addProgramVariable(v);
        }


        Map<LocationVariable,Term> atPres = HeapContext.getAtPres(atPreVars, services);

        //create variables for result and exception
        final ProgramVariable resultVar 
        	= inst.pm.isConstructor()
        	  ? TB.selfVar(services, inst.staticType, true)
                  : TB.resultVar(services, inst.pm, true);
        if(resultVar != null) {
            goal.addProgramVariable(resultVar);
        }
        assert inst.pm.isConstructor() 
               || !(inst.actualResult != null && resultVar == null);
        final ProgramVariable excVar = TB.excVar(services, inst.pm, true);
        assert excVar != null;
        goal.addProgramVariable(excVar);
        
        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        //translate the contract
        final Term contractSelf 
        	= OpReplacer.replace(TB.getBaseHeap(services), 
        		             atPres.get(baseHeap),
        		             inst.pm.isConstructor() 
        		               ? TB.var(resultVar) 
        		               : inst.actualSelf);
        final ImmutableList<Term> contractParams
        	= OpReplacer.replace(TB.getBaseHeap(services), 
        			    atPres.get(baseHeap), 
        			    inst.actualParams);
        final Term contractResult
        	= inst.pm.isConstructor() || resultVar == null 
        	  ? null 
                  : TB.var(resultVar);
        Map<LocationVariable, Term> heapTerms = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : heapContext) {
           heapTerms.put(h, TB.var(h));
        }
        final Term pre  = contract.getPre(heapContext,
                                          heapTerms, 
        				  contractSelf, 
        				  contractParams,
                                          atPres,
        				  services);
        final Term post = contract.getPost(heapContext,
                                           heapTerms,
        	                               contractSelf, 
        				                   contractParams, 
                                           contractResult, 
                                           TB.var(excVar), 
                                           atPres,
                                           services);
        final Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();

        for(LocationVariable heap : heapContext) {
           final Term m = contract.getMod(heap, TB.var(heap),
                contractSelf,contractParams, services);
           mods.put(heap, m);
        }

        final Term mby = contract.hasMby() 
                         ? contract.getMby(TB.getBaseHeap(services), 
                        	 	   contractSelf, 
                        	 	   contractParams, 
                        	 	   services) 
                         : null;
        
        //split goal into three/four branches
        final ImmutableList<Goal> result;
        final Goal preGoal, postGoal, excPostGoal, nullGoal;
        final ReferencePrefix rp = inst.mr.getReferencePrefix();
        if(rp != null 
           && !(rp instanceof ThisReference) 
           && !(rp instanceof SuperReference)
           && !(rp instanceof TypeReference)
           && !(inst.pm.isStatic())) {
            result = goal.split(4);
            postGoal = result.tail().tail().tail().head();
            excPostGoal = result.tail().tail().head();
            preGoal = result.tail().head();
            nullGoal = result.head();
            nullGoal.setBranchLabel("Null reference (" 
        	                    + inst.actualSelf 
        	                    + " = null)");
        } else {
            result = goal.split(3);
            postGoal = result.tail().tail().head();
            excPostGoal = result.tail().head();
            preGoal = result.head();
            nullGoal = null;
        }
        preGoal.setBranchLabel("Pre"+ " ("+contract.getTarget().getName()+")");
        postGoal.setBranchLabel("Post"+ " ("+contract.getTarget().getName()+")");
        excPostGoal.setBranchLabel("Exceptional Post"+ " ("+contract.getTarget().getName()+")");
        
        //prepare common stuff for the three branches
        Term anonAssumption = null;
        Term anonUpdate = null;
        Term wellFormedAnon = null;
        Term atPreUpdates = null;
        Term reachableState = null;
        ImmutableList<AnonUpdateData> anonUpdateDatas =
                ImmutableSLList.<AnonUpdateData>nil();

        for(LocationVariable heap : heapContext) {
           final AnonUpdateData tAnon;
           // TODO probably the special case still needs fixing (later)
           if(heap == baseHeap && !contract.hasModifiesClause()) {
             tAnon = new AnonUpdateData(TB.tt(), TB.skip(), TB.var(heap), TB.var(heap), TB.var(heap));
           }else{
             tAnon = createAnonUpdate(heap, inst.pm, mods.get(heap), services);
           }
           anonUpdateDatas = anonUpdateDatas.append(tAnon);
           if(anonAssumption == null) {
             anonAssumption = tAnon.assumption;
           }else{
             anonAssumption = TB.and(anonAssumption, tAnon.assumption);
           }
           if(anonUpdate == null) {
             anonUpdate = tAnon.anonUpdate;
           }else{
             anonUpdate = TB.parallel(anonUpdate, tAnon.anonUpdate);
           }
           if(wellFormedAnon == null) {
             wellFormedAnon = TB.wellFormed(tAnon.anonHeap,services);
           }else{
             wellFormedAnon = TB.and(wellFormedAnon, TB.wellFormed(tAnon.anonHeap,services));
           }
           final Term up = TB.elementary(services, atPreVars.get(heap), TB.var(heap));
           if(atPreUpdates == null) {
             atPreUpdates = up;
           }else{
             atPreUpdates = TB.parallel(atPreUpdates, up);
           }
           if(reachableState == null) {
             reachableState = TB.wellFormed(heap, services);
           }else{
             reachableState = TB.and(reachableState, TB.wellFormed(heap, services));
           }
        }

        final Term excNull = TB.equals(TB.var(excVar), TB.NULL(services));
        final Term excCreated = TB.created(services, TB.var(excVar));
        final Term freePost = getFreePost(inst.pm,
	    		     		  inst.staticType,
	    		     		  contractResult,
	    		     		  contractSelf,
	    		     		  atPres.get(baseHeap),
	    		     		  services);  
        final Term freeExcPost = inst.pm.isConstructor() 
                                 ? freePost 
                                 : TB.tt();        
        final Term postAssumption 
        	= TB.applySequential(new Term[]{inst.u, atPreUpdates}, 
        		   	     TB.and(anonAssumption,
        		   		    TB.apply(anonUpdate,
        		   	                     TB.and(new Term[]{excNull, 
                                	     	                       freePost, 
                                	     	                       post}))));
        final Term excPostAssumption 
        	= TB.applySequential(new Term[]{inst.u, atPreUpdates}, 
        		   TB.and(anonAssumption,
                                  TB.apply(anonUpdate,
                                           TB.and(new Term[]{TB.not(excNull),
                                	     	             excCreated, 
                                	     	             freeExcPost, 
                                	     	             post}))));
       
        // prepare information flow analysis
        assert anonUpdateDatas.size() == 1; // information flow extension is at
                                            // the moment not compatible with
                                            // the non-base-heap setting
        Term contractApplPredTerm =
                storePrePostInPredAndGenInfoFlowTaclet(contract, inst,
                                                       anonUpdateDatas.head(),
                                                       contractSelf,
                                                       contractResult,
                                                       TB.var(excVar),
                                                       goal, services);

        //create "Pre" branch
	int i = 0;
	for(Term arg : contractParams) {
	    KeYJavaType argKJT = contract.getTarget().getParameterType(i++);
	    reachableState = TB.and(reachableState,
		                    TB.reachableValue(services, arg, argKJT));
	}
	final ContractPO po 
		= services.getSpecificationRepository()
		          .getPOForProof(goal.proof());
	final Term mbyOk;	
	if(po != null && po.getMbyAtPre() != null && mby != null ) {
    	mbyOk = TB.and(TB.leq(TB.zero(services), mby, services), 
    			       TB.lt(mby, po.getMbyAtPre(), services));
	} else {
	    mbyOk = TB.tt();
	}
        preGoal.changeFormula(new SequentFormula(
        			TB.applySequential(new Term[]{inst.u, atPreUpdates}, 
        	                                   TB.and(new Term[]{pre, 
        	                                	   	     reachableState, 
        	                                	   	     mbyOk}))),
                              ruleApp.posInOccurrence());
       
        //create "Post" branch
	final StatementBlock resultAssign;
	if(inst.actualResult == null) {
	    resultAssign = new StatementBlock();
	} else {
	    final CopyAssignment ca 
	    	= new CopyAssignment(inst.actualResult, resultVar);
	    resultAssign = new StatementBlock(ca);
	}        
        final StatementBlock postSB 
        	= replaceStatement(jb, resultAssign);
        final Term normalPost 
            	= TB.apply(anonUpdate,
                           TB.prog(inst.mod,
                                   JavaBlock.createJavaBlock(postSB),
                                   inst.progPost.sub(0)));
        postGoal.addFormula(new SequentFormula(wellFormedAnon), 
        	            true, 
        	            false);
        postGoal.changeFormula(new SequentFormula(TB.apply(inst.u, 
        						       normalPost)),
        	               ruleApp.posInOccurrence());
        postGoal.addFormula(new SequentFormula(postAssumption), 
        	            true, 
        	            false);
        postGoal.addFormula(new SequentFormula(contractApplPredTerm),
                            true,
                            false);


        
        //create "Exceptional Post" branch
        final StatementBlock excPostSB 
            = replaceStatement(jb, new StatementBlock(new Throw(excVar)));
        final Term excPost
            = TB.apply(anonUpdate,
                       TB.prog(inst.mod,
                               JavaBlock.createJavaBlock(excPostSB), 
                               inst.progPost.sub(0)));
        excPostGoal.addFormula(new SequentFormula(wellFormedAnon), 
                	       true, 
                	       false);        
        excPostGoal.changeFormula(new SequentFormula(TB.apply(inst.u, 
        						          excPost)),
        	                  ruleApp.posInOccurrence());        
        excPostGoal.addFormula(new SequentFormula(excPostAssumption), 
        	               true, 
        	               false);
        
        
        //create "Null Reference" branch
        if(nullGoal != null) {
            final Term actualSelfNotNull 
            	= TB.not(TB.equals(inst.actualSelf, TB.NULL(services)));
            nullGoal.changeFormula(new SequentFormula(TB.apply(
        	    				inst.u, 
        					actualSelfNotNull)),
        	                   ruleApp.posInOccurrence());                    
        }
        
        //create justification
        final RuleJustificationBySpec just 
        	= new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust 
            	= (ComplexRuleJustificationBySpec)
            	    goal.proof().env().getJustifInfo().getJustification(this);
        cjust.add(ruleApp, just);
        return result;
    }
    
    
    @Override    
    public Name name() {
        return NAME;
    }


    @Override    
    public String displayName() { 
        return NAME.toString();
    }
    

    @Override
    public String toString() {
        return displayName();
    }
    

    /**
     * Store pre- / poststate of the method invocation and generate information
     * flow taclet.
     */
    // TODO: add exception var
    private Term storePrePostInPredAndGenInfoFlowTaclet(final FunctionalOperationContract contract,
                                                        final Instantiation inst,
                                                        final AnonUpdateData anonUpdateData,
                                                        final Term contractSelf,
                                                        final Term contractResult,
                                                        final Term exceptionVar,
                                                        final Goal goal,
                                                        final Services services) {
        ProofObligationVars appData =
                new ProofObligationVars(contractSelf, null, inst.actualParams,
                                        contractResult, null, exceptionVar,
                                        null, null,
                                        anonUpdateData.methodHeapAtPre,
                                        anonUpdateData.methodHeap, "", services);
        BasicPOSnippetFactory f =
                POSinppetFactory.getBasicFactory(contract, appData, services);
        final Term contractApplPredTerm =
                f.create(BasicPOSnippetFactory.Snippet.TWO_STATE_METHOD_PRED);
        final Term updatedContractApplPredTerm =
                TB.apply(inst.u, contractApplPredTerm);

        final Function contApplPred = (Function)contractApplPredTerm.op();
        final Taclet informationFlowContractApp =
                genInfFlowContractApplTaclet(contract, contApplPred, inst.pm,
                                             inst.u, services);
        goal.addTaclet(informationFlowContractApp,
                       SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        return updatedContractApplPredTerm;
    }

    
    /*private Function generateContApplPredicate(IProgramMethod pm,
                                               Services services) {
        String nameString =
                MiscTools.toValidTacletName(pm.getContainerType().getFullName()
                + "::" + pm.getFullName() + "__RELATES").toString();
        final Name name = new Name(nameString);
        Function pred = (Function) services.getNamespaces().functions().lookup(
                name);
        if (pred == null) {
            // Arguments: params, heapAtPre, exception, heapAtPost
            int length = pm.getParamTypes().size() + 3;
            if (!pm.isStatic()) {
                // Arguments: + self
                length++;
            }
            if (!pm.isVoid() && !pm.isConstructor()) {
                // Arguments: + result
                length++;
            }
            Sort[] predArgSorts =
                    new Sort[length];

            int i = 0;
            if (!pm.isStatic()) {
                // type of self
                predArgSorts[i++] = pm.getContainerType().getSort();
            }
            // types of params
            for (KeYJavaType t : pm.getParamTypes()) {
                predArgSorts[i++] = t.getSort();
            }
            // type of heapAtPre
            predArgSorts[i++] = TB.getBaseHeap(services).sort();
            if (!pm.isVoid() && !pm.isConstructor()) {
                // type of result
                predArgSorts[i++] = pm.getReturnType().getSort();
            }
            // type of exception
            predArgSorts[i++] = services.getJavaInfo().getTypeByClassName(
                    "java.lang.Exception").getSort();
            // type of heapAtPost
            predArgSorts[i++] = TB.getBaseHeap(services).sort();

            pred = new Function(name, Sort.FORMULA, predArgSorts);
            services.getNamespaces().functions().addSafely(pred);
        }
        return pred;*/

    
    private ProofObligationVars generateApplicationDataSVs(Function pred,
                                                           String schemaPrefix,
                                                           IProgramMethod pm,
                                                           Services services) {
        Sort[] predArgSorts = new Sort[pred.argSorts().size()];
        pred.argSorts().toArray(predArgSorts);
        ImmutableList<Term> paramsSVs = ImmutableSLList.<Term>nil();

        int i = 0;
        Term selfAtPreSV;
        if (!pm.isStatic()) {
            selfAtPreSV = createTermSV(schemaPrefix + "_self",
                                       predArgSorts[i], services);
            i++;
        } else {
            selfAtPreSV = null;
        }
        int j = 0;
        for (KeYJavaType t : pm.getParamTypes()) {
            predArgSorts[i] = t.getSort();
            paramsSVs =
                    paramsSVs.append(createTermSV(schemaPrefix + "_param_" +
                                                  (j + 1), predArgSorts[i],
                                                  services));
            i++;
            j++;
        }
        Term heapAtPreSV = createTermSV(schemaPrefix + "_heapAtPre",
                                        predArgSorts[i], services);
        i++;
        Term resSV = null;
        if (!pm.isVoid() && !pm.isConstructor()) {
            resSV = createTermSV(schemaPrefix + "_res", predArgSorts[i],
                                 services);
            i++;
        }
        Term exceptionSV = createTermSV(schemaPrefix + "_exception",
                                        predArgSorts[i], services);
        i++;
        Term heapAtPostSV = createTermSV(schemaPrefix + "_heapAtPost",
                                         predArgSorts[i], services);
        i++;

        return new ProofObligationVars(selfAtPreSV, selfAtPreSV, paramsSVs, resSV,
                                       resSV, exceptionSV, exceptionSV, heapAtPreSV,
                                       heapAtPreSV, heapAtPostSV, "", services);
    }
    
    
    private Taclet genInfFlowContractApplTaclet(FunctionalOperationContract contract,
                                                Function contractApplPred,
                                                IProgramMethod pm,
                                                Term stateUpdate,
                                                Services services) {
        Name tacletName =
                MiscTools.toValidTacletName("Use information flow contract for "
                + pm.getFullName());

        ProofObligationVars schemaDataFind = generateApplicationDataSVs(
                contractApplPred, "find", pm, services);
        ProofObligationVars schemaDataAssumes = generateApplicationDataSVs(
                contractApplPred, "assumes", pm, services);
        BasicPOSnippetFactory fFind =
                POSinppetFactory.getBasicFactory(contract, schemaDataFind, services);
        BasicPOSnippetFactory fAssumes =
                POSinppetFactory.getBasicFactory(contract, schemaDataAssumes, services);
        Term schemaFind =
                TB.apply(stateUpdate, fFind.create(BasicPOSnippetFactory.Snippet.TWO_STATE_METHOD_PRED));
        Term schemaAssumes =
                TB.apply(stateUpdate, fAssumes.create(BasicPOSnippetFactory.Snippet.TWO_STATE_METHOD_PRED));

        ImmutableSet<InformationFlowContract> ifContracts =
                getInfromFlowContracts(pm, services);
        Term schemaContApps =
                buildContractApplications(ifContracts, schemaDataFind,
                                          schemaDataAssumes, services);
        
        //create sequents
        Sequent assumesSeq = Sequent.createAnteSequent(
                new Semisequent(new SequentFormula(schemaAssumes)));
        Sequent axiomSeq = Sequent.createAnteSequent(
                new Semisequent(new SequentFormula(schemaContApps)));
        
        //create taclet
        RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(schemaFind); // TODO: is this correct? has to match only in the antecedent!
        tacletBuilder.setIfSequent(assumesSeq);
        RewriteTacletGoalTemplate goal =
                new RewriteTacletGoalTemplate(axiomSeq,
                                              ImmutableSLList.<Taclet>nil(),
                                              schemaFind);
        tacletBuilder.addTacletGoalTemplate(goal);
        tacletBuilder.addRuleSet(new RuleSet(new Name("information_flow_contract_appl")));
        tacletBuilder.setSurviveSmbExec(true);
        return tacletBuilder.getTaclet();
    }
    
    
    private ImmutableSet<InformationFlowContract> getInfromFlowContracts(
            IProgramMethod pm,
            Services services) {
        ImmutableSet<Contract> contracts =
                services.getSpecificationRepository().getContracts(
                pm.getContainerType(), pm);
        ImmutableSet<InformationFlowContract> ifContracts =
                DefaultImmutableSet.<InformationFlowContract>nil();
        for(Contract c : contracts) {
            if (c instanceof InformationFlowContract) {
                ifContracts = ifContracts.add((InformationFlowContract)c);
            }
        }
        return ifContracts;
    }    


    private Term createTermSV(String svName,
                              Sort predArgSort,
                              Services services) {
        Name name = services.getVariableNamer().getTemporaryNameProposal(svName);
        return TB.var(SchemaVariableFactory.createTermSV(name, predArgSort));
    }
        

    public Term buildContractApplications(
            ImmutableSet<InformationFlowContract> targetContracts,
            ProofObligationVars contAppData,
            ProofObligationVars contAppData2,
            Services services) {
        ImmutableList<Term> contractsApplications = ImmutableSLList.<Term>nil();
        for (InformationFlowContract cont : targetContracts) {
            contractsApplications = contractsApplications.append(
                    buildContractApplication(cont, contAppData,
                                             contAppData2, services));
        }
        return TB.and(contractsApplications);
    }


    private static Term buildContractApplication(InformationFlowContract cont,
                                                 ProofObligationVars contAppData,
                                                 ProofObligationVars contAppData2,
                                                 Services services) {
        BasicPOSnippetFactory f1 =
                POSinppetFactory.getBasicFactory(cont, contAppData, services);
        BasicPOSnippetFactory f2 =
                POSinppetFactory.getBasicFactory(cont, contAppData2, services);

        Term preCond1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        Term preCond2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);

        InfFlowPOSnippetFactory iff =
                POSinppetFactory.getInfFlowFactory(cont, contAppData,
                                                   contAppData2, services);
        Term inOutRelations =
                iff.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_POST);
        return TB.imp(TB.and(preCond1, preCond2), inOutRelations);
    }


    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------

    public static final class Instantiation {
	public final Term u;
	public final Term progPost;
	public final Modality mod;
	public final Expression actualResult;
	public final Term actualSelf;	
	public final KeYJavaType staticType;	
	public final MethodOrConstructorReference mr;
	public final IProgramMethod pm;
	public final ImmutableList<Term> actualParams;
	
	public Instantiation(Term u, 
			     Term progPost, 
			     Modality mod,
			     Expression actualResult,
			     Term actualSelf,
			     KeYJavaType staticType,
			     MethodOrConstructorReference mr,
			     IProgramMethod pm,
			     ImmutableList<Term> actualParams) {
	    assert u != null;
	    assert u.sort() == Sort.UPDATE;
	    assert progPost != null;
	    assert progPost.sort() == Sort.FORMULA;
	    assert mod != null;
	    assert mr != null;
	    assert pm != null;
	    assert actualParams != null;
	    this.u = u;
	    this.progPost = progPost;
	    this.mod = mod;
	    this.actualResult = actualResult;
	    this.actualSelf = actualSelf;
	    this.staticType = staticType;
	    this.mr = mr;
	    this.pm = pm;
	    this.actualParams = actualParams;
	}
    }



	@Override
    public ContractRuleApp createApp(PosInOccurrence pos) {
		return new ContractRuleApp(this, pos);
    }


    private static class AnonUpdateData {

        public final Term assumption, anonUpdate, methodHeap, methodHeapAtPre, anonHeap;


        public AnonUpdateData(Term assumption,
                              Term anonUpdate,
                              Term methodHeap,
                              Term methodHeapAtPre,
                              Term anonHeap) {
            this.assumption = assumption;
            this.anonUpdate = anonUpdate;
            this.methodHeap = methodHeap;
            this.methodHeapAtPre = methodHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }

}
