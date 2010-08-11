// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design

package de.uka.ilkd.key.rtsj.rule;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.rule.AbstractUseOperationContractRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRuleApp;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;

/**
 * Implements the rule which inserts operation contracts for a method body
 * statement.
 */
public class UseOperationContractRuleRTSJ extends
        AbstractUseOperationContractRule {

    private static final Name NAME = new Name("Use Operation Contract");
    public static final AbstractUseOperationContractRule INSTANCE_RTSJ_PURE = new UseOperationContractRuleRTSJ(false);
    public static final AbstractUseOperationContractRule INSTANCE_RTSJ_MEM = new UseOperationContractRuleRTSJ(true);
    private final boolean memoryConsumptionAware;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private UseOperationContractRuleRTSJ(boolean memoryConsumptionAware) {
	this.memoryConsumptionAware = memoryConsumptionAware;
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    public ImmutableList<Goal> apply(Goal goal, Services services,
	    RuleApp ruleApp) {
	// collect information about sequent
	final PosInOccurrence pio = goBelowUpdates(ruleApp.posInOccurrence());
	final Modality modality = (Modality) pio.subTerm().op();
	final JavaBlock jb = pio.subTerm().javaBlock();
	final SourceElement activeStatement = getActiveStatement(jb);

	final MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
	final ProgramMethod pm = mbs.getProgramMethod(services);
	final Term actualSelf = (mbs.getDesignatedContext() instanceof Expression ? services
	        .getTypeConverter().convertToLogicElement(
	                mbs.getDesignatedContext()) : null);

	final ImmutableList<Term> actualParams = getMethodArgumentsAsTerms(
	        services, mbs);

	ProgramVariable actualResult = (ProgramVariable) mbs
	        .getResultVariable();

	// configure contract and assumed / ensured invariants
	ContractWithInvs cwi;
	if (ruleApp instanceof UseOperationContractRuleApp) {
	    // the contract and invariants are already fixed
	    // (probably because we're in the process of reading in a
	    // proof from a file)
	    cwi = ((UseOperationContractRuleApp) ruleApp).getInstantiation();
	} else {
	    cwi = configureContract(services, pm, modality, pio);
	}
	if (cwi == null) {
	    return null;
	}

	assert cwi.contract.getProgramMethod().equals(pm) : "Tries to apply contract for "
	        + cwi.contract.getProgramMethod() + " to " + pm;

	// create variables for self, parameters, result, exception, and a map
	// for atPre-functions
	// register the newly created program variables
	Namespace progVarNS = services.getNamespaces().programVariables();
	ProgramVariable selfVar = SVF.createSelfVar(services, pm, true);
	if (selfVar != null) {
	    goal.addProgramVariable(selfVar);
	}

	ImmutableList<ParsableVariable> paramVars = SVF.createParamVars(
	        services, pm, true);
	ImmutableList<ProgramVariable> paramVarsAsProgVars = ImmutableSLList
	        .<ProgramVariable> nil();
	for (ParsableVariable pvar : paramVars) {
	    assert pvar instanceof ProgramVariable : pvar
		    + " is not a ProgramVariable";
	    paramVarsAsProgVars = paramVarsAsProgVars
		    .append((ProgramVariable) pvar);
	    goal.addProgramVariable((ProgramVariable) pvar);
	}

	ProgramVariable resultVar = SVF.createResultVar(services, pm, true);

	if (resultVar != null) {
	    goal.addProgramVariable(resultVar);
	}

	ProgramVariable excVar = SVF.createExcVar(services, pm, true);
	if (excVar != null) {
	    progVarNS.addSafely(excVar);
	}

	Map<Operator, Function> atPreFunctions = new LinkedHashMap<Operator, Function>();

	ExecutionContext ec = getExecutionContext(pio);
	Term mTerm =  services.getTypeConverter().convertToLogicElement(
		    ec.getMemoryAreaAsRef(), ec);

	// translate the contract and the invariants
	FormulaWithAxioms pre = getPreconditionAndInvariants(services, pm, cwi,
                selfVar, paramVars, mTerm);

	FormulaWithAxioms post = getPostconditionAndInvariants(services, cwi,
                selfVar, paramVars, resultVar, excVar, atPreFunctions, mTerm);

	ImmutableSet<LocationDescriptor> modifies = getModifies(services,
                actualParams, cwi, selfVar, paramVars);

	// Store the node info before the node is split
	final NodeInfo ni = goal.node().getNodeInfo();

	// split goal into three branches
	ImmutableList<Goal> result = goal.split(3);
	Goal preGoal = result.tail().tail().head();
	preGoal.setBranchLabel("Pre");
	Goal postGoal = result.tail().head();
	postGoal.setBranchLabel("Post");
	Goal excPostGoal = result.head();
	excPostGoal.setBranchLabel("Exceptional Post");

	// prepare common stuff for the three branches
	UpdateFactory uf = new UpdateFactory(services, goal.simplifier());
	AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
	ImmutableSet<Metavariable> mvs = getAllMetavariables(pio.topLevel()
	        .subTerm());
	Term[] mvTerms = new Term[mvs.size()];
	final Iterator<Metavariable> it2 = mvs.iterator();
	for (int i = 0; i < mvTerms.length; i++) {
	    assert it2.hasNext();
	    mvTerms[i] = TB.func(it2.next());
	}

	Update selfParamsUpdate = (selfVar == null ? uf.skip() : uf
	        .elementaryUpdate(TB.var(selfVar), actualSelf));

	Term[] argTerms = new Term[paramVars.size() + (pm.isStatic() ? 0 : 1)];
	int i = 0;

	if (!pm.isStatic()) {
	    argTerms[i++] = TB.var(selfVar);
	}

	final Iterator<Term> actualParamsIt = actualParams.iterator();
	for (final ParsableVariable paramVar : paramVars) {
	    assert actualParamsIt.hasNext();
	    selfParamsUpdate = uf.parallel(selfParamsUpdate, uf
		    .elementaryUpdate(TB.var(paramVar), actualParamsIt.next()));
	    argTerms[i++] = TB.var(paramVar);
	}

	Update anonUpdate = auf.createAnonymisingUpdate(modifies, mvTerms,
	        services);

	Term wsEq = TB.tt();

	if (memoryConsumptionAware) {
	    NamespaceSet nss = services.getNamespaces();
	    Function add = (Function) nss.functions().lookup(new Name("add"));

	    Term mCons = getConsumedMemoryTerm(services, mTerm);
	    Term ws = getWorkingspace(pm, argTerms, nss);

	    wsEq = TB.equals(ws,
		    cwi.contract.getWorkingSpace(selfVar, paramVars, services));

	    Update wsUpd = uf.elementaryUpdate(mCons, TB.tf()
		    .createFunctionTerm(add, mCons, ws));
	    anonUpdate = wsUpd == null ? anonUpdate : uf.parallel(anonUpdate,
		    wsUpd);
	}

	Update atPreUpdate = APF.createAtPreDefinitions(atPreFunctions,
	        services);

	Term excNullTerm = TB.equals(TB.var(excVar), TB.NULL(services));

	// create "Pre" branch
	Term preF = pre.getFormula();

	if (memoryConsumptionAware) {
	    NamespaceSet nss = services.getNamespaces();
	    Function leq = (Function) nss.functions().lookup(new Name("leq"));
	    Function add = (Function) nss.functions().lookup(new Name("add"));
	    Term wsPre = cwi.contract.getWorkingSpace(selfVar, paramVars,
		    services);

	    wsPre = TB.tf().createFunctionTerm(
		    leq,
		    TB.tf().createFunctionTerm(add,
		            getConsumedMemoryTerm(services, mTerm), wsPre),
		    TB.dot(mTerm,
		            services.getJavaInfo().getAttribute("size",
		                    "javax.realtime.MemoryArea")));

	    preF = wsPre;
	}

	Term preTerm = createPrecondition(services, selfVar,
	        paramVarsAsProgVars, preF, pre.getAxiomsAsFormula(), selfParamsUpdate, uf);

	replaceInGoal(preTerm, preGoal, pio);

	// create "Post" branch
	Term postTerm = createNormalTerminationBranch(services, pio, modality,
	        jb, actualResult, resultVar, post, ni, uf, selfParamsUpdate,
	        anonUpdate, atPreUpdate, excNullTerm);

	if (memoryConsumptionAware) {
	    wsEq = uf.apply(uf.sequential(new Update[] { selfParamsUpdate,
		    atPreUpdate }), wsEq);
	    postTerm = TB.imp(wsEq, postTerm);
	}

	replaceInGoal(postTerm, postGoal, pio);

	// create "Exceptional Post" branch
	Term excPostTerm = createExceptionalBranch(services, pio, modality, jb,
	        excVar, post, uf, selfParamsUpdate, anonUpdate, atPreUpdate);

	excPostTerm = TB.imp(wsEq, excPostTerm);

	replaceInGoal(excPostTerm, excPostGoal, pio);

	// create justification
	createJustification(goal, ruleApp, cwi);

	return result;
    }

    public Name name() {
	return NAME;
    }

    public String displayName() {
	return NAME.toString();
    }

    public String toString() {
	return displayName();
    }
}
