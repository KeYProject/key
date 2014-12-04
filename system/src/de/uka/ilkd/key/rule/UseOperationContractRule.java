// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
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
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.init.StateVars;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.InfFlowMethodContractTacletBuilder;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.Pair;


/**
 * Implements the rule which inserts operation contracts for a method call.
 */
public final class UseOperationContractRule implements BuiltInRule {
    /**
     * Hint to refactor the final pre term.
     */
    public static final String FINAL_PRE_TERM_HINT = "finalPreTerm";

    public static final UseOperationContractRule INSTANCE
                                            = new UseOperationContractRule();

    private static final Name NAME = new Name("Use Operation Contract");

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;


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
    private static AnonUpdateData createAnonUpdate(LocationVariable heap,
                                                   IProgramMethod pm, 
	                                     	   Term mod, 
	                                     	   Services services) {
	assert pm != null;
	assert mod != null;
	final TermBuilder TB = services.getTermBuilder();

	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name methodHeapName = new Name(TB.newName(heap+"After_" + pm.getName()));
	final Function methodHeapFunc = new Function(methodHeapName, heapLDT.targetSort(), true);
	services.getNamespaces().functions().addSafely(methodHeapFunc);
	final Term methodHeap = TB.func(methodHeapFunc);
	final Name anonHeapName = new Name(TB.newName("anon_" + heap + "_" + pm.getName()));
	final Function anonHeapFunc = new Function(anonHeapName, heap.sort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeap = TB.label(TB.func(anonHeapFunc), ParameterlessTermLabel.ANON_HEAP_LABEL);
	final Term assumption =
	        TB.equals(TB.anon(TB.var(heap), mod, anonHeap),
                          methodHeap); 
	final Term anonUpdate = TB.elementary(heap, methodHeap);

	return new AnonUpdateData(assumption, anonUpdate, methodHeap,
	                          TB.getBaseHeap(), anonHeap);
    }

    /**
     * Construct a free postcondition for the given method,
     * i.e., a postcondition that is always true as guaranteed by the Java language
     * and is not required to be checked by the callee.
     * For constructors, it states that the self term is created and not null in the poststate
     * and it has not been created in the prestate.
     * For regular methods, it states that the return value is in range,
     * meaning created or null for reference types, inInt(), etc., for integer types,
     * and for location sets containing only locations that belong to created objects.
     */
    private static Term getFreePost(List<LocationVariable> heapContext, IProgramMethod pm,
	    		     	    KeYJavaType kjt,
	    		     	    Term resultTerm,
	    		     	    Term selfTerm,
	    		     	    Map<LocationVariable, Term> heapAtPres,
	    		     	    Services services) {
        final TermBuilder TB = services.getTermBuilder();
        final Term result;
        if(pm.isConstructor()) {
            assert resultTerm == null;
            assert selfTerm != null;
            Term createdForm = null;
            for(LocationVariable heap : heapContext) {
            	if(heap == services.getTypeConverter().getHeapLDT().getSavedHeap()) {
            		continue;
            	}
            	final Term cr = TB.and(OpReplacer.replace(TB.var(heap),
	                  	 heapAtPres.get(heap),
	                   	 TB.not(TB.created(TB.var(heap), selfTerm)), 
	                   	 services.getTermFactory()),
                         TB.created(TB.var(heap), selfTerm));
            	if(createdForm == null) {
            		createdForm = cr;
            	}else{
            		createdForm = TB.and(createdForm, cr);
            	}
            }
            result = TB.and(TB.not(TB.equals(selfTerm, TB.NULL())),
                    createdForm,
                    TB.exactInstance(kjt.getSort(), selfTerm));
        } else if(resultTerm != null) {
            result = TB.reachableValue(resultTerm,
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


    private static Instantiation instantiate(Term focusTerm, Services services) {
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

    private static void applyInfFlow(Goal goal,
                                     final FunctionalOperationContract contract,
                                     final Instantiation inst,
                                     final Term self,
                                     final ImmutableList<Term> params,
                                     final Term result,
                                     final Term exception,
                                     final Term mby,
                                     final Term atPreUpdates,
                                     final Term finalPreTerm,
                                     final ImmutableList<AnonUpdateData> anonUpdateDatas,
                                     Services services) {
        if (!InfFlowCheckInfo.isInfFlow(goal)) {
            return;
        }

        // prepare information flow analysis
        assert anonUpdateDatas.size() == 1 : "information flow extension " +
                                             "is at the moment not " +
                                             "compatible with the " +
                                             "non-base-heap setting";
        AnonUpdateData anonUpdateData = anonUpdateDatas.head();

        final Term heapAtPre = anonUpdateData.methodHeapAtPre;
        final Term heapAtPost = anonUpdateData.methodHeap;

        // generate proof obligation variables
        final boolean hasSelf = self != null;
        final boolean hasRes = result != null;
        final boolean hasExc = exception != null;

        final StateVars preVars =
                new StateVars(hasSelf ? self : null,
                              params,
                              hasRes ? result : null,
                              hasExc ? exception : null,
                              heapAtPre, mby);
        final StateVars postVars =
                new StateVars(hasSelf ? self : null,
                              params,
                              hasRes ? result : null,
                              hasExc ? exception : null,
                              heapAtPost, mby);
        final ProofObligationVars poVars =
                new ProofObligationVars(preVars, postVars, services);

        // generate information flow contract application predicate
        // and associated taclet
        InfFlowMethodContractTacletBuilder ifContractBuilder =
                new InfFlowMethodContractTacletBuilder(services);
        ifContractBuilder.setContract(contract);
        ifContractBuilder.setContextUpdate(atPreUpdates, inst.u);
        ifContractBuilder.setProofObligationVars(poVars);

        Term contractApplPredTerm = ifContractBuilder.buildContractApplPredTerm();
        Taclet informationFlowContractApp = ifContractBuilder.buildTaclet();

        // add term and taclet to post goal
        goal.addFormula(new SequentFormula(contractApplPredTerm),
                true,
                false);
        goal.addTaclet(informationFlowContractApp,
                SVInstantiations.EMPTY_SVINSTANTIATIONS, true);

        // information flow proofs might get easier if we add the (proved)
        // method contract precondition as an assumption to the post goal
        // (in case the precondition cannot be proved easily)
        goal.addFormula(new SequentFormula(finalPreTerm), true, false);
        goal.proof().addIFSymbol(contractApplPredTerm);
        goal.proof().addIFSymbol(informationFlowContractApp);
        goal.proof().addGoalTemplates(informationFlowContractApp);
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
   final TermBuilder TB = services.getTermBuilder();
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
	assert pm != null : "Getting program method failed.\nReference: " + mr +
	                    ", static type: "+staticType+", execution context: " + ec;
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
	        actualParams,
	        mod == Modality.DIA_TRANSACTION || mod == Modality.BOX_TRANSACTION);
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

	// abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
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

        // contract can be applied if modality is box and needs no termination
        // argument
        // see #1417, BOX_TRANSACTION added according to Wojciech's proposal.
        if(inst.mod == Modality.BOX || inst.mod == Modality.BOX_TRANSACTION) {
            return true;
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
        final TermBuilder tb = services.getTermBuilder();

        //configure contract
        final FunctionalOperationContract contract =
        		(FunctionalOperationContract)((AbstractContractRuleApp) ruleApp)
                .getInstantiation();
        assert contract.getTarget().equals(inst.pm);

        final List<LocationVariable> heapContext =
                HeapContext.getModHeaps(goal.proof().getServices(), inst.transaction);

	//prepare heapBefore_method
        Map<LocationVariable,LocationVariable> atPreVars =
                computeAtPreVars(heapContext, services, inst);
        for(LocationVariable v : atPreVars.values()) {
     	  goal.addProgramVariable(v);
        }

        Map<LocationVariable,Term> atPres = HeapContext.getAtPres(atPreVars, services);

        //create variables for result and exception
        final ProgramVariable resultVar = computeResultVar(inst, services); 
        if(resultVar != null) {
            goal.addProgramVariable(resultVar);
        }
        assert inst.pm.isConstructor()
               || !(inst.actualResult != null && resultVar == null);
        final ProgramVariable excVar = tb.excVar(inst.pm, true);
        assert excVar != null;
        goal.addProgramVariable(excVar);

        LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
        //translate the contract
        final Term baseHeapTerm = tb.getBaseHeap();
        final ImmutableList<Term> contractParams = computeParams(baseHeapTerm, atPres, baseHeap, inst, tb.tf());
        final Term contractResult
        	= inst.pm.isConstructor() || resultVar == null
        	  ? null
                  : tb.var(resultVar);
        final Term contractSelf = computeSelf(baseHeapTerm, atPres, baseHeap, 
                inst, contractResult == null && resultVar != null ? tb.var(resultVar) : contractResult,
                services.getTermFactory());
        Map<LocationVariable, Term> heapTerms = new LinkedHashMap<LocationVariable,Term>();
        for(LocationVariable h : heapContext) {
           heapTerms.put(h, tb.var(h));
        }
        final Term globalDefs = contract.getGlobalDefs(baseHeap, baseHeapTerm, contractSelf,
                                                       contractParams, services);
        final Term originalPre  = contract.getPre(heapContext,
                                          heapTerms,
        				  contractSelf,
        				  contractParams,
                                          atPres,
        				  services);
        final Term pre = globalDefs==null? originalPre: tb.apply(globalDefs, originalPre);
        final Term originalPost = contract.getPost(heapContext,
                                           heapTerms,
        	                               contractSelf,
        				                   contractParams,
                                           contractResult,
                                           tb.var(excVar),
                                           atPres,
                                           services);
        final Term post = globalDefs==null? originalPost: tb.apply(globalDefs, originalPost);
        final Map<LocationVariable,Term> mods = new LinkedHashMap<LocationVariable,Term>();

        for(LocationVariable heap : heapContext) {
           final Term m = contract.getMod(heap, tb.var(heap),
                contractSelf,contractParams, services);
           mods.put(heap, m);
        }

        final Term mby = contract.hasMby()
                         ? contract.getMby(heapTerms,
                        	 	   contractSelf,
                        	 	   contractParams,
                        	 	   atPres,
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
           if (!contract.hasModifiesClause(heap)) {
             tAnon = new AnonUpdateData(tb.tt(), tb.skip(), tb.var(heap), tb.var(heap), tb.var(heap));
           } else {
             tAnon = createAnonUpdate(heap, inst.pm, mods.get(heap), services);
           }
           anonUpdateDatas = anonUpdateDatas.append(tAnon);
           if (anonAssumption == null) {
             anonAssumption = tAnon.assumption;
           } else {
             anonAssumption = tb.and(anonAssumption, tAnon.assumption);
           }
           if (anonUpdate == null) {
             anonUpdate = tAnon.anonUpdate;
           } else {
             anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);
           }
           if (wellFormedAnon == null) {
             wellFormedAnon = tb.wellFormed(tAnon.anonHeap);
           } else {
             wellFormedAnon = tb.and(wellFormedAnon, tb.wellFormed(tAnon.anonHeap));
           }
           final Term up = tb.elementary(atPreVars.get(heap), tb.var(heap));
           if(atPreUpdates == null) {
             atPreUpdates = up;
           }else{
             atPreUpdates = tb.parallel(atPreUpdates, up);
           }
           if(reachableState == null) {
             reachableState = tb.wellFormed(heap);
           }else{
             reachableState = tb.and(reachableState, tb.wellFormed(heap));
           }
        }

        final Term excNull = tb.equals(tb.var(excVar), tb.NULL());
        final Term excCreated = tb.created(tb.var(excVar));
        final Term freePost = getFreePost(heapContext,
                              inst.pm,
	    		     		  inst.staticType,
	    		     		  contractResult,
	    		     		  contractSelf,
	    		     		  atPres,
	    		     		  services);
        final Term freeExcPost = inst.pm.isConstructor()
                                 ? freePost
                                 : tb.tt();
        final Term postAssumption
        	= tb.applySequential(new Term[]{inst.u, atPreUpdates},
        		   	     tb.and(anonAssumption,
        		   		    tb.apply(anonUpdate, tb.and(excNull,
                                    freePost,
                                    post), null)));
        final Term excPostAssumption
        	= tb.applySequential(new Term[]{inst.u, atPreUpdates},
        		   tb.and(anonAssumption,
                                  tb.apply(anonUpdate, tb.and(tb.not(excNull),
                                          excCreated,
                                          freeExcPost,
                                          post), null)));

        //create "Pre" branch
	int i = 0;
	for(Term arg : contractParams) {
	    KeYJavaType argKJT = contract.getTarget().getParameterType(i++);
	    reachableState = tb.and(reachableState,
		                    tb.reachableValue(arg, argKJT));
	}

        Term finalPreTerm;
        if(!InfFlowCheckInfo.isInfFlow(goal)) {
            final ContractPO po
                    = services.getSpecificationRepository()
                              .getPOForProof(goal.proof());

            final Term mbyOk;
         // see #1417
            if(inst.mod != Modality.BOX && inst.mod != Modality.BOX_TRANSACTION && po != null && mby != null ) {
//          mbyOk = TB.and(TB.leq(TB.zero(services), mby, services),
//                                 TB.lt(mby, po.getMbyAtPre(), services));
//              mbyOk = TB.prec(mby, po.getMbyAtPre(), services);
                mbyOk = tb.measuredByCheck(mby);
            } else {
                mbyOk = tb.tt();
            }
            finalPreTerm =
                    tb.applySequential(new Term[]{inst.u, atPreUpdates},
                                       tb.and(new Term[]{pre,
                                                         reachableState,
                                                         mbyOk}));
        } else {
            // termination has already been shown in the functional proof,
            // thus we do not need to show it again in information flow proofs.
            finalPreTerm =
                    tb.applySequential(new Term[]{inst.u, atPreUpdates},
                                                  tb.and(new Term[]{pre,
                                                                    reachableState}));
        }

        finalPreTerm = TermLabelManager.refactorTerm(services, null, finalPreTerm, this, preGoal, FINAL_PRE_TERM_HINT, null);
        preGoal.changeFormula(new SequentFormula(finalPreTerm),
                              ruleApp.posInOccurrence());

        TermLabelManager.refactorLabels(services, ruleApp.posInOccurrence(), this, preGoal, null, null);

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
        JavaBlock postJavaBlock = JavaBlock.createJavaBlock(postSB);
        final Term normalPost = tb.apply(anonUpdate,
                                         tb.prog(inst.mod,
                                                 postJavaBlock,
                                                 inst.progPost.sub(0),
                                                 TermLabelManager.instantiateLabels(
                                                         services, ruleApp.posInOccurrence(), this,
                                                         postGoal, "PostModality", null, inst.mod,
                                                         new ImmutableArray<Term>(inst.progPost.sub(0)),
                                                         null, postJavaBlock, inst.progPost.getLabels())
                                                 ),
                                         null);
        postGoal.addFormula(new SequentFormula(wellFormedAnon),
        	            true,
        	            false);
        postGoal.changeFormula(new SequentFormula(tb.apply(inst.u, normalPost, null)),
        	               ruleApp.posInOccurrence());
        postGoal.addFormula(new SequentFormula(postAssumption),
        	            true,
        	            false);

        applyInfFlow(postGoal, contract, inst, contractSelf, contractParams, contractResult,
                     tb.var(excVar), mby, atPreUpdates,finalPreTerm, anonUpdateDatas, services);

        //create "Exceptional Post" branch
        final StatementBlock excPostSB
            = replaceStatement(jb, new StatementBlock(new Throw(excVar)));
        JavaBlock excJavaBlock = JavaBlock.createJavaBlock(excPostSB);
        final Term originalExcPost = tb.apply(anonUpdate,
                                              tb.prog(inst.mod, excJavaBlock, inst.progPost.sub(0),
                                                      TermLabelManager.instantiateLabels(services,
                                                              ruleApp.posInOccurrence(), this,
                                                              excPostGoal, "ExceptionalPostModality",
                                                              null, inst.mod,
                                                              new ImmutableArray<Term>(
                                                                      inst.progPost.sub(0)),
                                                              null, excJavaBlock, inst.progPost.getLabels())), null);
        final Term excPost = globalDefs==null? originalExcPost: tb.apply(globalDefs, originalExcPost);
        excPostGoal.addFormula(new SequentFormula(wellFormedAnon),
                	       true,
                	       false);
        excPostGoal.changeFormula(new SequentFormula(tb.apply(inst.u, excPost, null)),
        	                  ruleApp.posInOccurrence());
        excPostGoal.addFormula(new SequentFormula(excPostAssumption),
        	               true,
        	               false);


        //create "Null Reference" branch
        if(nullGoal != null) {
            final Term actualSelfNotNull
            	= tb.not(tb.equals(inst.actualSelf, tb.NULL()));
            nullGoal.changeFormula(new SequentFormula(tb.apply(inst.u, 
        					               actualSelfNotNull,
        					               null)),
        	                   ruleApp.posInOccurrence());
        }

        TermLabelManager.refactorLabels(services, ruleApp.posInOccurrence(), this, nullGoal, null, null);



        //create justification
        final RuleJustificationBySpec just
        	= new RuleJustificationBySpec(contract);
        final ComplexRuleJustificationBySpec cjust
            	= (ComplexRuleJustificationBySpec)
            	    goal.proof().getInitConfig().getJustifInfo().getJustification(this);
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
	public final boolean transaction;

	public Instantiation(Term u,
			     Term progPost,
			     Modality mod,
			     Expression actualResult,
			     Term actualSelf,
			     KeYJavaType staticType,
			     MethodOrConstructorReference mr,
			     IProgramMethod pm,
			     ImmutableList<Term> actualParams,
			     boolean transaction) {
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
	    this.transaction = transaction;
	}
    }

    public ContractRuleApp createApp(PosInOccurrence pos) {
       return createApp(pos, null);
    }

    @Override
    public ContractRuleApp createApp(PosInOccurrence pos, TermServices services) {
		return new ContractRuleApp(this, pos);
    }

   public static Map<LocationVariable, LocationVariable> computeAtPreVars(List<LocationVariable> heapContext, 
                                                                          TermServices services, 
                                                                          Instantiation inst) {
      return HeapContext.getBeforeAtPreVars(heapContext, services, "Before_"+inst.pm.getName());
   }

   public static Term computeSelf(Term baseHeapTerm, 
                                  Map<LocationVariable,Term> atPres, 
                                  LocationVariable baseHeap, 
                                  Instantiation inst, 
                                  Term resultTerm, TermFactory tf) {
      return OpReplacer.replace(baseHeapTerm,
                                atPres.get(baseHeap),
                                inst.pm.isConstructor() ? resultTerm : inst.actualSelf, tf);
   }

   public static ImmutableList<Term> computeParams(Term baseHeapTerm, 
                                                   Map<LocationVariable,Term> atPres, 
                                                   LocationVariable baseHeap, 
                                                   Instantiation inst,
                                                   TermFactory tf) {
      return OpReplacer.replace(baseHeapTerm, atPres.get(baseHeap), inst.actualParams, tf);
   }

   public static ProgramVariable computeResultVar(Instantiation inst, TermServices services) {
      final TermBuilder TB = services.getTermBuilder();
      return inst.pm.isConstructor() ? 
             TB.selfVar(inst.staticType, true) : 
             TB.resultVar(inst.pm, true);
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