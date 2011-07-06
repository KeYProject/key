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

import java.util.HashMap;
import java.util.Map;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

public final class WhileInvariantRule implements BuiltInRule {

    public static final WhileInvariantRule INSTANCE = new WhileInvariantRule();

    private static final Name NAME = new Name("Loop Invariant");
    private static final TermBuilder TB = TermBuilder.DF;

    private Term lastFocusTerm;
    private Instantiation lastInstantiation;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private WhileInvariantRule() {
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private Instantiation instantiate(Term focusTerm, Services services) {
	if (focusTerm == lastFocusTerm
	        && lastInstantiation.inv == services
	                .getSpecificationRepository().getLoopInvariant(
	                        lastInstantiation.loop)) {
	    return lastInstantiation;
	}

	// leading update?
	final Term u;
	final Term progPost;
	if (focusTerm.op() instanceof UpdateApplication) {
	    u = UpdateApplication.getUpdate(focusTerm);
	    progPost = UpdateApplication.getTarget(focusTerm);
	} else {
	    u = TB.skip();
	    progPost = focusTerm;
	}

	// focus (below update) must be modality term
	if (progPost.op() != Modality.BOX && progPost.op() != Modality.DIA) {
	    return null;
	}

	// active statement must be while loop
	SourceElement activeStatement = MiscTools.getActiveStatement(progPost
	        .javaBlock());
	if (!(activeStatement instanceof While)) {
	    return null;
	}
	final While loop = (While) activeStatement;

	LoopInvariant inv = services.getSpecificationRepository()
	        .getLoopInvariant(loop);

	System.out.println("winvrule: 101");
	System.out.println(inv == null);
	System.out.println("u = " + u.toString());
	/*if (inv != null) {
	    System.out.println("Heap = "
		    + inv.getInternalHeapAtPre().toString()
		    + "\n"
		    + "selfTerm = "
		    + inv.getInternalSelfTerm().toString()
		    + "\n"
		    + "inv = "
		    + inv.getInvariant(inv.getInternalSelfTerm(), inv
		            .getInternalHeapAtPre(), services)
		    + "\n"
		    + "mod = "
		    + inv.getModifies(inv.getInternalSelfTerm(), inv
		            .getInternalHeapAtPre(), services)
		    + "\n"
		    + "var = "
		    + inv.getVariant(inv.getInternalSelfTerm(), inv
		            .getInternalHeapAtPre(), services));
	}*/

	// New
	if (inv == null) {
	    System.out.println("winvrule 115 1 branch");
	    inv = new LoopInvariantImpl(loop,
		    MiscTools.getInnermostMethodFrame(progPost.javaBlock(),
		            services) == null ? null : MiscTools.getSelfTerm(
		            MiscTools.getInnermostMethodFrame(progPost
		                    .javaBlock(), services), services),
		    (Term) null);
	    inv = Main.getInstance().getLoopInvariant(inv, services);
	} else if (inv.getInvariant(inv.getInternalSelfTerm(), inv
	        .getInternalHeapAtPre(), services) == null) {// Invariant
	    // is
	    // needed
	    System.out.println("winvrule 125 2 branch");
	    inv = Main.getInstance().getLoopInvariant(inv, services, false);

	} else if (progPost.op() == Modality.DIA
	        && inv.getVariant(inv.getInternalSelfTerm(), inv
	                .getInternalHeapAtPre(), services) == null) { // Variant
	    // is
	    // needed

	    System.out.println("winvrule 136 3 branch");

	    inv = Main.getInstance().getLoopInvariant(inv, services, true);

	}
	// Old

	// collect self, execution context
	final MethodFrame innermostMethodFrame = MiscTools
	        .getInnermostMethodFrame(progPost.javaBlock(), services);
	final Term selfTerm = innermostMethodFrame == null ? null : MiscTools
	        .getSelfTerm(innermostMethodFrame, services);
	final ExecutionContext innermostExecutionContext = innermostMethodFrame == null ? null
	        : (ExecutionContext) innermostMethodFrame.getExecutionContext();

	// cache and return result
	System.out.println("invrule: 162");
	Instantiation result = new Instantiation(u, progPost, loop, inv,
	        selfTerm, innermostExecutionContext);
	lastFocusTerm = focusTerm;
	lastInstantiation = result;
	return result;
    }

    /**
     * @return (anon update, anon heap)
     */
    private Pair<Term, Term> createAnonUpdate(While loop, Term mod,
	    ImmutableSet<ProgramVariable> localOuts, Services services) {
	// heap
	final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final Name anonHeapName = new Name(TB
	        .newName(services, "anonHeap_loop"));
	final Function anonHeapFunc = new Function(anonHeapName, heapLDT
	        .targetSort());
	services.getNamespaces().functions().addSafely(anonHeapFunc);
	final Term anonHeapTerm = TB.func(anonHeapFunc);
	Term anonUpdate = TB.anonUpd(services, mod, anonHeapTerm);

	// local output vars
	for (ProgramVariable pv : localOuts) {
	    final String anonFuncName = TB.newName(services, pv.name()
		    .toString());
	    final Function anonFunc = new Function(new Name(anonFuncName), pv
		    .sort());
	    services.getNamespaces().functions().addSafely(anonFunc);
	    final Term elemUpd = TB.elementary(services, (LocationVariable) pv,
		    TB.func(anonFunc));
	    anonUpdate = TB.parallel(anonUpdate, elemUpd);
	}

	return new Pair<Term, Term>(anonUpdate, anonHeapTerm);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
	// focus must be top level succedent
	if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
	    return false;
	}

	// instantiation must succeed
	Instantiation inst = instantiate(pio.subTerm(), goal.proof()
	        .getServices());
	return inst != null;
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
	    RuleApp ruleApp) {
	final KeYJavaType booleanKJT = services.getTypeConverter()
	        .getBooleanType();
	final KeYJavaType intKJT = services.getJavaInfo()
	        .getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT);

	// get instantiation
	Instantiation inst = instantiate(ruleApp.posInOccurrence().subTerm(),
	        services);
	final Term heapAtMethodPre = inst.inv.getInternalHeapAtPre();
	final Term invTerm = inst.inv.getInvariant(inst.selfTerm,
	        heapAtMethodPre, services);
	final Term mod = inst.inv.getModifies(inst.selfTerm, heapAtMethodPre,
	        services);
	final Term variant = inst.inv.getVariant(inst.selfTerm,
	        heapAtMethodPre, services);

	// collect input and output local variables,
	// prepare reachableIn and reachableOut
	final ImmutableSet<ProgramVariable> localIns = MiscTools.getLocalIns(
	        inst.loop, services);
	final ImmutableSet<ProgramVariable> localOuts = MiscTools.getLocalOuts(
	        inst.loop, services);
	Term reachableIn = TB.tt();
	for (ProgramVariable pv : localIns) {
	    reachableIn = TB.and(reachableIn, TB.reachableValue(services, pv));
	}
	Term reachableOut = TB.tt();
	for (ProgramVariable pv : localOuts) {
	    reachableOut = TB
		    .and(reachableOut, TB.reachableValue(services, pv));
	}

	// prepare heapBeforeLoop, localOutBeforeLoop
	final LocationVariable heapBeforeLoop = TB.heapAtPreVar(services,
	        "heapBeforeLoop", true);
	services.getNamespaces().programVariables().addSafely(heapBeforeLoop);
	Term beforeLoopUpdate = TB.elementary(services, heapBeforeLoop, TB
	        .heap(services));
	final Map<Term, Term> normalToBeforeLoop = new HashMap<Term, Term>();
	normalToBeforeLoop.put(TB.heap(services), TB.var(heapBeforeLoop));
	for (ProgramVariable pv : localOuts) {
	    final String pvBeforeLoopName = TB.newName(services, pv.name()
		    .toString()
		    + "BeforeLoop");
	    final LocationVariable pvBeforeLoop = new LocationVariable(
		    new ProgramElementName(pvBeforeLoopName), pv
		            .getKeYJavaType());
	    services.getNamespaces().programVariables().addSafely(pvBeforeLoop);
	    beforeLoopUpdate = TB.parallel(beforeLoopUpdate, TB.elementary(
		    services, pvBeforeLoop, TB.var(pv)));
	    normalToBeforeLoop.put(TB.var(pv), TB.var(pvBeforeLoop));
	}

	// prepare anon update, frame condition
	final Pair<Term, Term> anonUpdateAndHeap = createAnonUpdate(inst.loop,
	        mod, localOuts, services);
	final Term anonUpdate = anonUpdateAndHeap.first;
	final Term anonHeap = anonUpdateAndHeap.second;
	final Term frameCondition = TB.frame(services, normalToBeforeLoop, mod);

	// prepare variant
	final ProgramElementName variantName = new ProgramElementName(TB
	        .newName(services, "variant"));
	final LocationVariable variantPV = new LocationVariable(variantName,
	        intKJT);
	services.getNamespaces().programVariables().addSafely(variantPV);
	final boolean dia = inst.progPost.op() == Modality.DIA;
	final Term variantUpdate = dia ? TB.elementary(services, variantPV,
	        variant) : TB.skip();
	final Term variantNonNeg = dia ? TB.leq(TB.zero(services), variant,
	        services) : TB.tt();
	final Term variantPO = dia ? TB.and(variantNonNeg, TB.lt(variant, TB
	        .var(variantPV), services)) : TB.tt();

	// split goal into three branches
	ImmutableList<Goal> result = goal.split(3);
	Goal initGoal = result.tail().tail().head();
	Goal bodyGoal = result.tail().head();
	Goal useGoal = result.head();
	initGoal.setBranchLabel("Invariant Initially Valid");
	bodyGoal.setBranchLabel("Body Preserves Invariant");
	useGoal.setBranchLabel("Use Case");

	// prepare guard
	final ProgramElementName guardVarName = new ProgramElementName(TB
	        .newName(services, "b"));
	final LocationVariable guardVar = new LocationVariable(guardVarName,
	        booleanKJT);
	services.getNamespaces().programVariables().addSafely(guardVar);
	final VariableSpecification guardVarSpec = new VariableSpecification(
	        guardVar, inst.loop.getGuardExpression(), booleanKJT);
	final LocalVariableDeclaration guardVarDecl = new LocalVariableDeclaration(
	        new TypeRef(booleanKJT), guardVarSpec);
	final Statement guardVarMethodFrame = inst.innermostExecutionContext == null ? guardVarDecl
	        : new MethodFrame(null, inst.innermostExecutionContext,
	                new StatementBlock(guardVarDecl));
	final JavaBlock guardJb = JavaBlock.createJavaBlock(new StatementBlock(
	        guardVarMethodFrame));
	final Term guardTrueTerm = TB.equals(TB.var(guardVar), TB
	        .TRUE(services));
	final Term guardFalseTerm = TB.equals(TB.var(guardVar), TB
	        .FALSE(services));

	// prepare common assumption
	final Term[] uAnon = new Term[] { inst.u, anonUpdate };
	final Term[] uBeforeLoopDefAnonVariant = new Term[] { inst.u,
	        beforeLoopUpdate, anonUpdate, variantUpdate };
	final Term uAnonInv = TB.applySequential(uAnon, TB.and(invTerm,
	        reachableOut));
	final Term uAnonInvVariantNonNeg = TB.applySequential(uAnon, TB
	        .and(new Term[] { invTerm, reachableOut, variantNonNeg }));

	// "Invariant Initially Valid":
	// \replacewith (==> inv );
	final Term reachableState = TB.and(TB.wellFormedHeap(services),
	        reachableIn);
	initGoal.changeFormula(new SequentFormula(TB.apply(inst.u, TB.and(
	        invTerm, reachableState))), ruleApp.posInOccurrence());

	// "Body Preserves Invariant":
	// \replacewith (==> #atPreEqs(anon1)
	// -> #introNewAnonUpdate(#modifies, #locDepFunc(anon1, \[{.. while (#e)
	// #s ...}\]post) & inv ->
	// (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]#v1=TRUE ->
	// #whileInvRule(\[{.. while (#e) #s ...}\]post,
	// #locDepFunc(anon1, \[{.. while (#e) #s ...}\]post) & inv)),anon1));
	bodyGoal.addFormula(new SequentFormula(TB
	        .wellFormed(services, anonHeap)), true, false);

	bodyGoal.addFormula(new SequentFormula(uAnonInvVariantNonNeg), true,
	        false);

	final WhileInvRule wir = (WhileInvRule) AbstractTermTransformer.WHILE_INV_RULE;
	SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS
	        .replace(null, null, inst.innermostExecutionContext, null,
	                services);
	for (SchemaVariable sv : wir.neededInstantiations(inst.loop, svInst)) {
	    assert sv instanceof ProgramSV;
	    svInst = svInst.addInteresting(sv, (Name) new ProgramElementName(sv
		    .name().toString()), services);
	}
	Term bodyTerm = TB.tf().createTerm(wir, inst.progPost,
	        TB.and(new Term[] { invTerm, frameCondition, variantPO }));
	bodyTerm = wir.transform(bodyTerm, svInst, services);
	final Term guardTrueBody = TB.box(guardJb, TB.imp(guardTrueTerm,
	        bodyTerm));

	bodyGoal.changeFormula(new SequentFormula(TB.applySequential(
	        uBeforeLoopDefAnonVariant, guardTrueBody)), ruleApp
	        .posInOccurrence());

	// "Use Case":
	// \replacewith (==> #introNewAnonUpdate(#modifies, inv ->
	// (\[{ method-frame(#ex):{#typeof(#e) #v1 = #e;} }\]
	// (#v1=FALSE -> \[{.. ...}\]post)),anon2))
	useGoal.addFormula(
	        new SequentFormula(TB.wellFormed(services, anonHeap)), true,
	        false);
	useGoal.addFormula(new SequentFormula(uAnonInv), true, false);

	Term restPsi = TB.prog(dia ? Modality.DIA : Modality.BOX, MiscTools
	        .removeActiveStatement(inst.progPost.javaBlock(), services),
	        inst.progPost.sub(0));
	Term guardFalseRestPsi = TB.box(guardJb, TB
	        .imp(guardFalseTerm, restPsi));
	useGoal.changeFormula(new SequentFormula(TB.applySequential(uAnon,
	        guardFalseRestPsi)), ruleApp.posInOccurrence());

	return result;
    }

    @Override
    public Name name() {
	return NAME;
    }

    @Override
    public String displayName() {
	return toString();
    }

    @Override
    public String toString() {
	return NAME.toString();
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class Instantiation {
	public final Term u;
	public final Term progPost;
	public final While loop;
	public final LoopInvariant inv;
	public final Term selfTerm;
	public final ExecutionContext innermostExecutionContext;

	public Instantiation(Term u, Term progPost, While loop,
	        LoopInvariant inv, Term selfTerm,
	        ExecutionContext innermostExecutionContext) {
	    assert u != null;
	    assert u.sort() == Sort.UPDATE;
	    assert progPost != null;
	    assert progPost.sort() == Sort.FORMULA;
	    assert loop != null;
	    assert inv != null;
	    this.u = u;
	    this.progPost = progPost;
	    this.loop = loop;
	    this.inv = inv;
	    this.selfTerm = selfTerm;
	    this.innermostExecutionContext = innermostExecutionContext;
	}
    }
}
