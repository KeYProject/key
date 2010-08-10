// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.bugdetection.ContractAppInfo;
import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.gui.ContractConfigurator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.recoderext.ConstructorNormalformBuilder;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustificationBySpec;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;

public abstract class AbstractUseOperationContractRule implements BuiltInRule {

    protected static final TermBuilder TB = TermBuilder.DF;
    protected static final SignatureVariablesFactory SVF = SignatureVariablesFactory.INSTANCE;
    protected static final AtPreFactory APF = AtPreFactory.INSTANCE;
    private static final CreatedAttributeTermFactory CATF = CreatedAttributeTermFactory.INSTANCE;
    protected static final String INIT_NAME = ConstructorNormalformBuilder.CONSTRUCTOR_NORMALFORM_IDENTIFIER;

    /**
     * Returns a new PosInOccurrence which points to the same position as the
     * passed one, except below updates.
     */
    protected PosInOccurrence goBelowUpdates(PosInOccurrence pio) {
	if (pio != null && pio.subTerm().op() instanceof IUpdateOperator) {
	    int targetPos = ((IUpdateOperator) pio.subTerm().op()).targetPos();
	    return goBelowUpdates(pio.down(targetPos));
	} else {
	    return pio;
	}
    }

    /**
     * Returns the active statement of the passed a java block.
     */
    protected SourceElement getActiveStatement(JavaBlock jb) {
	assert jb.program() != null;

	SourceElement result = jb.program().getFirstElement();
	while (result instanceof ProgramPrefix
	        && !(result instanceof StatementBlock && ((StatementBlock) result)
	                .isEmpty())) {
	    if (result instanceof LabeledStatement) {
		result = ((LabeledStatement) result).getChildAt(1);
	    } else {
		result = result.getFirstElement();
	    }
	}
	return result;
    }

    /**
     * Returns all meta variables occurring in the passed term.
     */
    protected ImmutableSet<Metavariable> getAllMetavariables(Term term) {
	ImmutableSet<Metavariable> result = DefaultImmutableSet
	        .<Metavariable> nil();

	if (term.op() instanceof Metavariable) {
	    result = result.add((Metavariable) term.op());
	}

	for (int i = 0; i < term.arity(); i++) {
	    result = result.union(getAllMetavariables(term.sub(i)));
	}

	return result;
    }

    /**
     * Returns the operation contracts which are applicable for the passed
     * operation and the passed modality (at the passed PosInOccurrence).
     */
    private ImmutableSet<OperationContract> getApplicableContracts(
	    Services services, ProgramMethod pm, Modality modality,
	    PosInOccurrence pio) {
	ImmutableSet<OperationContract> result = services
	        .getSpecificationRepository().getOperationContracts(pm,
	                modality);

	// in box modalities, diamond contracts may be applied as well
	if (modality == Op.BOX) {
	    result = result.union(services.getSpecificationRepository()
		    .getOperationContracts(pm, Op.DIA));
	}

	// prevent application of contracts with "everything" modifier sets
	// if metavariables are involved (hackish, see Bug 810)
	if (getAllMetavariables(pio.topLevel().subTerm()).size() > 0) {
	    ProgramVariable dummySelfVar = SVF
		    .createSelfVar(services, pm, true);
	    ImmutableList<ParsableVariable> dummyParamVars = SVF
		    .createParamVars(services, pm, true);
	    for (OperationContract contract : result) {
		if (contract
		        .getModifies(dummySelfVar, dummyParamVars, services)
		        .contains(EverythingLocationDescriptor.INSTANCE)) {
		    result = result.remove(contract);
		}
	    }
	}

	return result;
    }

    /**
     * Chooses a contract to be applied together with invariants to be assumed
     * and ensured. This is done either automatically or by asking the user.
     */
    protected ContractWithInvs configureContract(Services services,
	    ProgramMethod pm, Modality modality, PosInOccurrence pio) {
	if (Main.getInstance().mediator().autoMode()) {
	    ImmutableSet<OperationContract> contracts = getApplicableContracts(
		    services, pm, modality, pio);
	    if (contracts.size() == 0) {
		return null;
	    }
	    OperationContract combinedContract = services
		    .getSpecificationRepository().combineContracts(contracts);

	    ImmutableSet<ClassInvariant> ownInvs = services
		    .getSpecificationRepository().getClassInvariants(
		            pm.getContainerType());

	    // TODO: Allow user control over the used invariants, instead of
	    // always using ownInvs (see bug #913)
	    return new ContractWithInvs(combinedContract, ownInvs, ownInvs);
	} else {
	    ContractConfigurator cc = new ContractConfigurator(
		    Main.getInstance(), services, pm, modality, true, true,
		    true, true);
	    if (cc.wasSuccessful()) {
		return cc.getContractWithInvs();
	    } else {
		return null;
	    }
	}
    }

    /**
     * Replaces the term at the passed PosInOccurrence with the passed
     * replacement in the passed goal.
     */
    protected void replaceInGoal(Term replacement, Goal goal,
	    PosInOccurrence pio) {
	final Map<Term, Term> replaceMap = new LinkedHashMap<Term, Term>();
	replaceMap.put(pio.subTerm(), replacement);
	OpReplacer or = new OpReplacer(replaceMap);

	ConstrainedFormula cf = pio.constrainedFormula();
	ConstrainedFormula newCf = new ConstrainedFormula(or.replace(cf
	        .formula()), cf.constraint());
	goal.changeFormula(newCf, pio);
    }

    private PosInProgram getPosInProgram(JavaBlock jb) {
	ProgramElement pe = jb.program();

	PosInProgram result = PosInProgram.TOP;

	if (pe instanceof ProgramPrefix) {
	    ProgramPrefix curPrefix = (ProgramPrefix) pe;

	    final ImmutableArray<ProgramPrefix> prefix = curPrefix
		    .getPrefixElements();
	    final int length = prefix.size();

	    // fail fast check
	    curPrefix = prefix.get(length - 1);// length -1 >= 0 as prefix array
		                               // contains curPrefix as first
					       // element

	    pe = curPrefix.getFirstActiveChildPos().getProgram(curPrefix);

	    assert pe instanceof MethodBodyStatement;

	    int i = length - 1;
	    do {
		result = curPrefix.getFirstActiveChildPos().append(result);
		i--;
		if (i >= 0) {
		    curPrefix = prefix.get(i);
		}
	    } while (i >= 0);

	} else {
	    assert pe instanceof MethodBodyStatement;
	}
	return result;
    }

    protected ExecutionContext getExecutionContext(PosInOccurrence pio) {
	if (pio == null) {
	    return null;
	}

	Term t = pio.subTerm();

	while (t.op() instanceof IUpdateOperator) {
	    pio = pio.down(((IUpdateOperator) t.op()).targetPos());
	    t = pio.subTerm();
	}

	if (!(t.op() instanceof Modality)) {
	    return null;
	}

	final ProgramElement pe = t.executableJavaBlock().program();

	if (pe == null) {
	    return null;
	}

	ProgramElement activeStatement = (Statement) pe;
	ExecutionContext ec = null;

	if (activeStatement instanceof ProgramPrefix) {

	    ProgramPrefix curPrefix = (ProgramPrefix) activeStatement;

	    final ImmutableArray<ProgramPrefix> prefix = curPrefix
		    .getPrefixElements();
	    final int length = prefix.size();

	    // fail fast check
	    curPrefix = prefix.get(length - 1);// length -1 >= 0 as prefix array
		                               // contains curPrefix as first
					       // element

	    activeStatement = curPrefix.getFirstActiveChildPos().getProgram(
		    curPrefix);

	    if (!(activeStatement instanceof MethodBodyStatement)) {
		return null;
	    }

	    int i = length - 1;
	    do {
		if (ec == null && curPrefix instanceof MethodFrame) {
		    ec = (ExecutionContext) ((MethodFrame) curPrefix)
			    .getExecutionContext();
		}
		i--;
		if (i >= 0) {
		    curPrefix = prefix.get(i);
		}
	    } while (i >= 0);

	} else if (!(activeStatement instanceof MethodBodyStatement)) {
	    return null;
	}
	return ec;
    }

    private StatementBlock replaceStatement(JavaBlock jb,
	    StatementBlock replacement) {
	PosInProgram pos = getPosInProgram(jb);
	int lastPos = pos.last();
	ContextStatementBlockInstantiation csbi = new ContextStatementBlockInstantiation(
	        pos, pos.up().down(lastPos + 1), null, jb.program());
	final NonTerminalProgramElement result = ProgramContextAdder.INSTANCE
	        .start((JavaNonTerminalProgramElement) jb.program(),
	                replacement, csbi);
	return (StatementBlock) result;
    }

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
	    Constraint userConstraint) {
	Services services = goal.node().proof().getServices();

	// pio must be a modality term in succedent
	pio = goBelowUpdates(pio);
	if (pio == null || pio.isInAntec()
	        || !(pio.subTerm().op() instanceof Modality)
	        || pio.subTerm().javaBlock().program() == null) {
	    return false;
	}

	// active statement must be method body statement (TODO: constructor
	// calls, see bug 702)
	Modality modality = (Modality) pio.subTerm().op();
	SourceElement activeStatement = getActiveStatement(pio.subTerm()
	        .javaBlock());
	if (!(activeStatement instanceof MethodBodyStatement)) {
	    return false;
	}

	// there must be applicable contracts for the operation
	MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
	ProgramMethod pm = mbs.getProgramMethod(services);
	ImmutableSet<OperationContract> contracts = getApplicableContracts(
	        services, pm, modality, pio);
	if (contracts.size() == 0) {
	    return false;
	}

	// applying a contract here must not create circular dependencies
	// between proofs
	if (!goal.proof().mgt().contractApplicableFor(pm, goal)) {
	    return false;
	}

	return true;
    }

    protected void createJustification(Goal goal, RuleApp ruleApp,
	    ContractWithInvs cwi) {
	RuleJustificationBySpec just = new RuleJustificationBySpec(cwi);
	ComplexRuleJustificationBySpec cjust = (ComplexRuleJustificationBySpec) goal
	        .proof().env().getJustifInfo().getJustification(this);
	cjust.add(ruleApp, just);
    }

    protected Term createPrecondition(Services services,
	    ProgramVariable selfVar,
	    ImmutableList<ProgramVariable> paramVarsAsProgVars,
	    Term pre, Term axioms, Update selfParamsUpdate,
	    UpdateFactory uf) {
	
	Term reachablePre = TB.and(new Term[] {
	        TB.inReachableState(services),
	        selfVar != null ? CATF.createCreatedAndNotNullTerm(services,
	                TB.var(selfVar)) : TB.tt(),
	        CATF.createReachableVariableValuesTerm(services,
	                paramVarsAsProgVars) });

	pre = TB.and(reachablePre, TB.imp(axioms, pre));

	Term preTerm = uf.prepend(selfParamsUpdate, pre);
	
	return preTerm;
    }

    protected Term createNormalTerminationBranch(Services services,
	    final PosInOccurrence pio, 
	    final Modality modality,
	    final JavaBlock jb, 
	    ProgramVariable actualResult,
	    ProgramVariable resultVar, 
	    FormulaWithAxioms post,
	    final NodeInfo ni, UpdateFactory uf, Update selfParamsUpdate,
	    Update anonUpdate, Update atPreUpdate, Term excNullTerm) {
	
	Term reachablePost = TB.and(TB.inReachableState(services),
	        CATF.createReachableVariableValueTerm(services, resultVar));
	StatementBlock postSB = replaceStatement(jb, new StatementBlock());

	final Term contractPost = TB.and(new Term[] { excNullTerm,
	        reachablePost, post.getAxiomsAsFormula(), post.getFormula() });

	Term postTermWithoutUpdate = TB.imp(contractPost, TB.prog(modality,
	        JavaBlock.createJavaBlock(postSB), pio.subTerm().sub(0)));

	final Update resultUpdate = (actualResult == null ? uf.skip() : uf
	        .elementaryUpdate(TB.var(actualResult), TB.var(resultVar)));

	// case distinction necessary because UpdateFactory is unable
	// to deal with update compositions involving both normal and
	// anonym*ous* updates; replace by "else" case once this is fixed
	Term postTerm;
	if (anonUpdate.isAnonymousUpdate()) {
	    postTerm = uf.prepend(resultUpdate, postTermWithoutUpdate);
	    postTerm = TB.tf().createAnonymousUpdateTerm(
		    AnonymousUpdate.getNewAnonymousOperator(), postTerm);
	} else {
	    postTerm = uf.prepend(
		    uf.sequential(new Update[] { selfParamsUpdate, atPreUpdate,
		            anonUpdate, resultUpdate }), postTermWithoutUpdate);
	}

	// //////////////////////////////////////////////////////////////
	// Store information about the contract rule application
	// for later use by the bugdetection package.
	// author:gladisch
	ContractAppInfo cInfo = new ContractAppInfo();
	cInfo.anon = anonUpdate;
	cInfo.contractPost = contractPost;
	if (anonUpdate.isAnonymousUpdate()) {
	    cInfo.prefix = resultUpdate;
	} else {
	    cInfo.prefix = uf.sequential(new Update[] { selfParamsUpdate,
		    atPreUpdate, resultUpdate });
	}
	ni.cInfo = cInfo;
	// //////////////////////////////////////////////////////////////
	return postTerm;
    }

    protected Term createExceptionalBranch(Services services,
	    final PosInOccurrence pio, final Modality modality,
	    final JavaBlock jb, ProgramVariable excVar, FormulaWithAxioms post,
	    UpdateFactory uf, Update selfParamsUpdate, Update anonUpdate,
	    Update atPreUpdate) {
	Term reachableExcPost = TB.and(TB.inReachableState(services),
	        CATF.createCreatedAndNotNullTerm(services, TB.var(excVar)));
	StatementBlock excPostSB = replaceStatement(jb, new StatementBlock(
	        new Throw(excVar)));
	Term excPostTermWithoutUpdate = TB.imp(
	        TB.and(new Term[] { reachableExcPost,
	                post.getAxiomsAsFormula(), post.getFormula() }), TB
	                .prog(modality, JavaBlock.createJavaBlock(excPostSB),
	                        pio.subTerm().sub(0)));
	Term excPostTerm = uf.prepend(
	        uf.sequential(new Update[] { selfParamsUpdate, atPreUpdate,
	                anonUpdate }), excPostTermWithoutUpdate);
	return excPostTerm;
    }

    protected Term getWorkingspace(final ProgramMethod pm, Term[] argTerms,
	    NamespaceSet nss) {
	Term ws = TB.tf().createWorkingSpaceNonRigidTerm(pm,
	        (Sort) nss.sorts().lookup(new Name("int")), argTerms);
	nss.functions().add(ws.op());
	return ws;
    }

    protected Term getConsumedMemoryTerm(Services services, Term mTerm) {
	Term mCons = null;
	mCons = TB.dot(
	        mTerm,
	        services.getJavaInfo().getAttribute("consumed",
	                "javax.realtime.MemoryArea"));
	return mCons;
    }

    protected ImmutableList<Term> getMethodArgumentsAsTerms(Services services,
	    final MethodBodyStatement mbs) {
	ImmutableList<Term> actualParams = ImmutableSLList.<Term> nil();

	for (Expression arg : mbs.getArguments()) {
	    actualParams = actualParams.append(services.getTypeConverter()
		    .convertToLogicElement(arg));
	}
	return actualParams;
    }

    protected ImmutableSet<LocationDescriptor> getModifies(Services services, final ImmutableList<Term> actualParams, ContractWithInvs cwi,
            ProgramVariable selfVar, ImmutableList<ParsableVariable> paramVars) {
                ImmutableSet<LocationDescriptor> modifies = cwi.contract.getModifies(
                        selfVar, paramVars, services);
            
                // add "actual parameters" (which in fact already are
                // program variables in a method body statement) to modifier set
                for (Term t : actualParams) {
                    ProgramVariable pv = (ProgramVariable) t.op();
                    modifies = modifies.add(new BasicLocationDescriptor(TB.var(pv)));
                }
                return modifies;
            }

    protected FormulaWithAxioms getPostconditionAndInvariants(Services services, ContractWithInvs cwi,
            ProgramVariable selfVar, ImmutableList<ParsableVariable> paramVars, ProgramVariable resultVar, ProgramVariable excVar, Map<Operator, Function> atPreFunctions,
            Term mTerm) {
                FormulaWithAxioms post = cwi.contract.getPost(selfVar, paramVars,
                        resultVar, excVar, mTerm, atPreFunctions, services);
            
                for (final ClassInvariant inv : cwi.ensuredInvs) {
                    post = post.conjoin(inv.getClosedInv(services));
                }
                return post;
            }

    protected FormulaWithAxioms getPreconditionAndInvariants(Services services, final ProgramMethod pm,
            ContractWithInvs cwi, ProgramVariable selfVar, ImmutableList<ParsableVariable> paramVars, Term mTerm) {
                FormulaWithAxioms pre = cwi.contract.getPre(selfVar, paramVars, mTerm,
                        services);
            
                if (pm.getName().equals(INIT_NAME)) {
                    for (final ClassInvariant inv : cwi.assumedInvs) {
                	pre = pre.conjoin(inv.getClosedInvExcludingOne(selfVar,
                	        services));
                    }
                } else {
                    for (final ClassInvariant inv : cwi.assumedInvs) {
                	pre = pre.conjoin(inv.getClosedInv(services));
                    }
                }
                return pre;
            }

}
