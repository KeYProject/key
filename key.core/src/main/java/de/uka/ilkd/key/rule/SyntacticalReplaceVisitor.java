/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Stack;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableArray;

/**
 * visitor for method {@link JTerm#execPostOrder(Visitor)}. Called with that
 * method
 * on a term, the visitor builds a new term replacing SchemaVariables with their instantiations that
 * are given as a SVInstantiations object.
 */
public class SyntacticalReplaceVisitor implements DefaultVisitor {
    public static final String SUBSTITUTION_WITH_LABELS_HINT = "SUBSTITUTION_WITH_LABELS";
    protected final SVInstantiations svInst;
    protected final Services services;
    /** the term builder used to construct terms */
    protected final TermBuilder tb;
    private JTerm computedResult = null;
    protected final PosInOccurrence applicationPosInOccurrence;
    protected final Rule rule;
    protected final Goal goal;
    protected final RuleApp ruleApp;

    protected final TermLabelState termLabelState;
    protected final TacletLabelHint labelHint;

    /**
     * the stack contains the subterms that will be added in the next step of execPostOrder in Term
     * in order to build the new term. A boolean value between or under the subterms on the stack
     * indicate that a term using these subterms should build a new term instead of using the old
     * one, because one of its subterms has been built, too.
     */
    private final Stack<Object> subStack; // of Term (and Boolean)
    private final Boolean newMarker = Boolean.TRUE;
    private final Deque<JTerm> tacletTermStack = new ArrayDeque<>();


    /**
     * constructs a term visitor replacing any occurrence of a schemavariable found in
     * {@code svInst} by its instantiation
     *
     * @param termLabelState the termlabel state
     * @param labelHint hints about how to deal with labels
     * @param applicationPosInOccurrence the application position
     * @param svInst mapping of schemavariables to their instantiation
     * @param goal the current goal
     * @param rule the applied rule
     * @param ruleApp the rule application
     * @param useTermCache the TermBuilder to use (allows to use the non cached version)
     */
    private SyntacticalReplaceVisitor(TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence,
            SVInstantiations svInst, Goal goal,
            Rule rule, RuleApp ruleApp, boolean useTermCache) {
        this.termLabelState = termLabelState;
        this.services = goal.getOverlayServices();
        this.tb = services.getTermBuilder(useTermCache);
        this.svInst = svInst;
        this.applicationPosInOccurrence = applicationPosInOccurrence;
        this.rule = rule;
        this.ruleApp = ruleApp;
        this.labelHint = labelHint;
        this.goal = goal;
        subStack = new Stack<>(); // of Term
        if (labelHint != null) {
            labelHint.setTacletTermStack(tacletTermStack);
        }
    }

    /**
     * ONLY TO BE USED BY ConstraintAwareSyntacticalReplaceVisitor (HACK)
     * constructs a term visitor replacing any occurrence of a schemavariable found in
     * {@code svInst} by its instantiation
     *
     * @param termLabelState the termlabel state
     * @param labelHint hints about how to deal with labels
     * @param applicationPosInOccurrence the application position
     * @param services the services
     * @param rule the applied rule
     * @param ruleApp the rule application
     * @param useTermCache the TermBuilder to use (allows to use the non cached version)
     */
    public SyntacticalReplaceVisitor(TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence,
            Services services,
            Rule rule, RuleApp ruleApp, boolean useTermCache) {
        this.termLabelState = termLabelState;
        this.services = services;
        this.tb = this.services.getTermBuilder(useTermCache);
        this.svInst = ruleApp instanceof TacletApp tacletApp ? tacletApp.instantiations()
                : SVInstantiations.EMPTY_SVINSTANTIATIONS;
        this.applicationPosInOccurrence = applicationPosInOccurrence;
        this.rule = rule;
        this.ruleApp = ruleApp;
        this.labelHint = labelHint;
        this.goal = null;
        subStack = new Stack<>(); // of Term
        if (labelHint != null) {
            labelHint.setTacletTermStack(tacletTermStack);
        }
    }

    /**
     * constructs a term visitor replacing any occurrence of a schemavariable found in
     * {@code svInst} by its instantiation
     *
     * @param termLabelState the termlabel state
     * @param labelHint hints about how to deal with labels
     * @param applicationPosInOccurrence the application position
     * @param svInst mapping of schemavariables to their instantiation
     * @param goal the current goal
     * @param rule the applied rule
     * @param ruleApp the rule application
     */
    public SyntacticalReplaceVisitor(TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence,
            SVInstantiations svInst, Goal goal,
            Rule rule, RuleApp ruleApp) {
        this(termLabelState, labelHint, applicationPosInOccurrence, svInst, goal, rule, ruleApp,
            true);
    }

    /**
     * ONLY used by {@link de.uka.ilkd.key.strategy.termgenerator.TriggeredInstantiations}
     *
     * @param termLabelState the termlabel state
     * @param svInst mapping of schemavariables to their instantiation
     * @param services the Services with information about the logic signature, access to term
     *        construction etc.
     */
    public SyntacticalReplaceVisitor(TermLabelState termLabelState, SVInstantiations svInst,
            Services services) {
        this.termLabelState = termLabelState;
        this.svInst = svInst;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.applicationPosInOccurrence = null;
        this.rule = null;
        this.goal = null;
        this.ruleApp = null;
        this.labelHint = null;
        subStack = new Stack<>();
    }

    private JavaProgramElement addContext(StatementBlock pe) {
        final ContextStatementBlockInstantiation cie = svInst.getContextInstantiation();
        if (cie == null) {
            throw new IllegalStateException("Context should also be instantiated");
        }

        if (cie.prefix() != null) {
            return ProgramContextAdder.INSTANCE.start(
                (JavaNonTerminalProgramElement) cie.program(), pe, cie);
        }

        return pe;
    }

    private JavaBlock replacePrg(SVInstantiations svInst, JavaBlock jb) {
        if (svInst.isEmpty()) {
            return jb;
        }

        ProgramReplaceVisitor trans;
        ProgramElement result;

        if (jb.program() instanceof ContextStatementBlock) {
            trans = new ProgramReplaceVisitor(
                new StatementBlock(((ContextStatementBlock) jb.program()).getBody()), // TODO
                services, svInst);
            trans.start();
            result = addContext((StatementBlock) trans.result());
        } else {
            trans = new ProgramReplaceVisitor(jb.program(), services, svInst);
            trans.start();
            result = trans.result();
        }
        return (result == jb.program()) ? jb : JavaBlock.createJavaBlock((StatementBlock) result);
    }

    private JTerm[] neededSubs(int n) {
        boolean newTerm = false;
        JTerm[] result = new JTerm[n];
        for (int i = n - 1; i >= 0; i--) {
            Object top = subStack.pop();
            if (top == newMarker) {
                newTerm = true;
                top = subStack.pop();
            }
            result[i] = (JTerm) top;
        }
        if (newTerm && (subStack.empty() || subStack.peek() != newMarker)) {
            subStack.push(newMarker);
        }
        return result;
    }


    protected void pushNew(Object t) {
        if (subStack.empty() || subStack.peek() != newMarker) {
            subStack.push(newMarker);
        }
        subStack.push(t);
    }

    /**
     * the method is only still invoked to allow the
     * {@link de.uka.ilkd.key.strategy.quantifierHeuristics.ConstraintAwareSyntacticalReplaceVisitor}
     * to recursively
     * replace meta variables
     */
    protected <T extends org.key_project.logic.Term> T toTerm(T o) {
        return o;
    }


    private ElementaryUpdate instantiateElementaryUpdate(ElementaryUpdate op) {
        final UpdateableOperator originalLhs = op.lhs();
        if (originalLhs instanceof SchemaVariable originalLhsAsSV) {
            Object lhsInst = svInst.getInstantiation(originalLhsAsSV);
            if (lhsInst instanceof JTerm lhsInstAsTerm) {
                lhsInst = lhsInstAsTerm.op();
            }

            final UpdateableOperator newLhs;
            if (lhsInst instanceof UpdateableOperator updateableLhs) {
                newLhs = updateableLhs;
            } else {
                assert false : "not updateable: " + lhsInst;
                throw new IllegalStateException("Encountered non-updateable operator " + lhsInst
                    + " on left-hand side of update.");
            }
            return newLhs == originalLhs ? op : ElementaryUpdate.getInstance(newLhs);
        } else {
            return op;
        }
    }


    private Operator instantiateModality(JModality op, JavaBlock jb) {
        JModality.JavaModalityKind kind = op.kind();
        if (op.kind() instanceof ModalOperatorSV) {
            kind = (JModality.JavaModalityKind) svInst.getInstantiation(op.kind());
        }
        if (jb != op.programBlock() || kind != op.kind()) {
            return JModality.getModality(kind, jb);
        }
        return op;
    }

    private Operator instantiateOperator(Operator p_operatorToBeInstantiated, JavaBlock jb) {
        Operator instantiatedOp = p_operatorToBeInstantiated;
        if (p_operatorToBeInstantiated instanceof SortDependingFunction sortDependingFunction) {
            instantiatedOp = handleSortDependingSymbol(sortDependingFunction);
        } else if (p_operatorToBeInstantiated instanceof ElementaryUpdate elementaryUpdate) {
            instantiatedOp = instantiateElementaryUpdate(elementaryUpdate);
        } else if (p_operatorToBeInstantiated instanceof JModality mod) {
            instantiatedOp = instantiateModality(mod, jb);
        } else if (p_operatorToBeInstantiated instanceof SchemaVariable opAsSV) {
            if (!(p_operatorToBeInstantiated instanceof ProgramSV opAsPSV) || !opAsPSV.isListSV()) {
                instantiatedOp = (Operator) svInst.getInstantiation(opAsSV);
            }
        }
        assert instantiatedOp != null;

        return instantiatedOp;
    }

    private ImmutableArray<QuantifiableVariable> instantiateBoundVariables(JTerm visited) {
        ImmutableArray<QuantifiableVariable> vBoundVars = visited.boundVars();
        if (!vBoundVars.isEmpty()) {
            final QuantifiableVariable[] newVars = new QuantifiableVariable[vBoundVars.size()];
            boolean varsChanged = false;

            for (int j = 0, size = vBoundVars.size(); j < size; j++) {
                QuantifiableVariable boundVar = vBoundVars.get(j);
                if (boundVar instanceof SchemaVariable boundSchemaVariable) {
                    final JTerm instantiationForBoundSchemaVariable =
                        (JTerm) svInst.getInstantiation(boundSchemaVariable);
                    // instantiation might be null in case of PO generation for taclets
                    if (instantiationForBoundSchemaVariable != null) {
                        boundVar = (QuantifiableVariable) instantiationForBoundSchemaVariable.op();
                        varsChanged = true;
                    }
                }
                newVars[j] = boundVar;
            }

            if (varsChanged) {
                vBoundVars = new ImmutableArray<>(newVars);
            }
        }
        return vBoundVars;
    }

    /**
     * performs the syntactic replacement of schemavariables with their instantiations
     */
    @Override
    public void visit(final Term p_visited) {
        final JTerm visited = (JTerm) p_visited;
        // Sort equality has to be ensured before calling this method
        final Operator visitedOp = visited.op();
        if (visitedOp instanceof SchemaVariable visitedSV && visitedOp.arity() == 0
                && svInst.isInstantiated(visitedSV)
                && (!(visitedOp instanceof ProgramSV visitedAsPSV && visitedAsPSV.isListSV()))) {
            final JTerm newTerm = toTerm(
                svInst.getTermInstantiation(visitedSV, svInst.getExecutionContext(), services));
            final JTerm labeledTerm = TermLabelManager.label(services, termLabelState,
                applicationPosInOccurrence, rule, ruleApp, goal, labelHint, visited, newTerm);
            pushNew(labeledTerm);
        } else {
            // instantiation of java block
            boolean jblockChanged = false;
            JavaBlock jb = visited.javaBlock();

            if (jb != JavaBlock.EMPTY_JAVABLOCK) {
                jb = replacePrg(svInst, jb);
                if (jb != visited.javaBlock()) {
                    jblockChanged = true;
                }
            }

            final Operator newOp = instantiateOperator(visitedOp, jb);

            // instantiate bound variables
            final ImmutableArray<QuantifiableVariable> boundVars =
                instantiateBoundVariables(visited);

            // instantiate sub terms
            final JTerm[] neededsubs = neededSubs(newOp != null ? newOp.arity() : 0);
            if (boundVars != visited.boundVars() || jblockChanged || (newOp != visitedOp)
                    || (!subStack.empty() && subStack.peek() == newMarker)) {
                final ImmutableArray<TermLabel> labels = instantiateLabels(visited, newOp,
                    new ImmutableArray<>(neededsubs), boundVars, visited.getLabels());
                final JTerm newTerm = tb.tf().createTerm(newOp, neededsubs, boundVars, labels);
                pushNew(resolveSubst(newTerm));
            } else {
                JTerm t;
                final ImmutableArray<TermLabel> labels = instantiateLabels(visited, visitedOp,
                    visited.subs(), visited.boundVars(), visited.getLabels());
                if (!visited.hasLabels() && labels != null && labels.isEmpty()) {
                    t = visited;
                } else {
                    t = tb.tf().createTerm(visitedOp, visited.subs(), visited.boundVars(),
                        labels);
                }
                t = resolveSubst(t);
                if (t == visited) {
                    subStack.push(t);
                } else {
                    pushNew(t);
                }
            }
        }
    }

    private ImmutableArray<TermLabel> instantiateLabels(JTerm tacletTerm, Operator newTermOp,
            ImmutableArray<JTerm> newTermSubs,
            ImmutableArray<QuantifiableVariable> newTermBoundVars,
            ImmutableArray<TermLabel> newTermOriginalLabels) {
        return TermLabelManager.instantiateLabels(termLabelState, services,
            applicationPosInOccurrence, rule, ruleApp, goal, labelHint, tacletTerm,
            tb.tf().createTerm(newTermOp, newTermSubs, newTermBoundVars, newTermOriginalLabels));
    }

    private Operator handleSortDependingSymbol(SortDependingFunction depOp) {
        final Sort depSort = depOp.getSortDependingOn();

        final Sort realDepSort =
            svInst.getGenericSortInstantiations().getRealSort(depSort, services);


        final Operator res = depOp.getInstanceFor(realDepSort, services);
        assert res != null
                : "Did not find instance of symbol " + depOp + " for sort " + realDepSort;
        return res;
    }

    private JTerm resolveSubst(JTerm t) {
        if (t.op() instanceof SubstOp) {
            JTerm resolved = ((SubstOp) t.op()).apply(t, tb);
            resolved = tb.label(resolved, t.sub(1).getLabels());
            if (t.hasLabels()) {
                resolved = TermLabelManager.refactorTerm(termLabelState, services, null, resolved,
                    rule, goal, SUBSTITUTION_WITH_LABELS_HINT, t);
            }
            return resolved;
        } else {
            return t;
        }
    }

    /**
     * delivers the new built term
     */
    public JTerm getTerm() {
        if (computedResult == null) {
            Object o;
            do {
                o = subStack.pop();
            } while (o == newMarker);
            // Term t = (Term) o;
            // CollisionDeletingSubstitutionTermApplier substVisit
            // = new CollisionDeletingSubstitutionTermApplier();
            // t.execPostOrder(substVisit);
            // t=substVisit.getTerm();
            computedResult = (JTerm) o;
        }
        return computedResult;
    }

    public SVInstantiations getSVInstantiations() {
        return svInst;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void subtreeEntered(Term subtreeRoot) {
        tacletTermStack.push((JTerm) subtreeRoot);
    }

    /**
     * this method is called in execPreOrder and execPostOrder in class Term when leaving the
     * subtree rooted in the term subtreeRoot. Default implementation is to do nothing. Subclasses
     * can override this method when the visitor behaviour depends on information bound to
     * subtrees.
     *
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */
    @Override
    public void subtreeLeft(Term subtreeRoot) {
        tacletTermStack.pop();
        if (subtreeRoot.op() instanceof TermTransformer mop) {
            final JTerm newTerm = mop.transform((JTerm) subStack.pop(), svInst, services);
            final JTerm labeledTerm = TermLabelManager.label(services, termLabelState,
                applicationPosInOccurrence, rule, ruleApp, goal, labelHint, (JTerm) subtreeRoot,
                newTerm);
            pushNew(labeledTerm);
        }
    }
}
