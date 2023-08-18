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
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SubstOp;
import de.uka.ilkd.key.logic.op.TermTransformer;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ConstraintAwareSyntacticalReplaceVisitor;

import org.key_project.util.collection.ImmutableArray;

/**
 * visitor for <t> execPostOrder </t> of {@link de.uka.ilkd.key.logic.Term}. Called with that method
 * on a term, the visitor builds a new term replacing SchemaVariables with their instantiations that
 * are given as a SVInstantiations object.
 */
public class SyntacticalReplaceVisitor extends DefaultVisitor {
    public static final String SUBSTITUTION_WITH_LABELS_HINT = "SUBSTITUTION_WITH_LABELS";
    protected final SVInstantiations svInst;
    protected final Services services;
    /** the termbuilder used to construct terms */
    protected final TermBuilder tb;
    private Term computedResult = null;
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
    private final Deque<Term> tacletTermStack = new ArrayDeque<>();


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
     * @param services the Services
     * @param termBuilder the TermBuilder to use (allows to use the non cached version)
     */
    private SyntacticalReplaceVisitor(TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence, SVInstantiations svInst, Goal goal,
            Rule rule, RuleApp ruleApp, Services services, TermBuilder termBuilder) {
        this.termLabelState = termLabelState;
        this.services = services;
        this.tb = termBuilder;
        this.svInst = svInst;
        this.applicationPosInOccurrence = applicationPosInOccurrence;
        this.rule = rule;
        this.ruleApp = ruleApp;
        this.labelHint = labelHint;
        this.goal = goal;
        subStack = new Stack<>(); // of Term
        if (labelHint instanceof TacletLabelHint) {
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
     * @param services the Services
     */
    public SyntacticalReplaceVisitor(TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence, SVInstantiations svInst, Goal goal,
            Rule rule, RuleApp ruleApp, Services services) {
        this(termLabelState, labelHint, applicationPosInOccurrence, svInst, goal, rule, ruleApp,
            services, services.getTermBuilder());
    }

    public SyntacticalReplaceVisitor(TermLabelState termLabelState, TacletLabelHint labelHint,
            PosInOccurrence applicationPosInOccurrence, Goal goal, Rule rule, RuleApp ruleApp,
            Services services, TermBuilder termBuilder) {
        this(termLabelState, labelHint, applicationPosInOccurrence,
            SVInstantiations.EMPTY_SVINSTANTIATIONS, goal, rule, ruleApp, services);
    }

    private JavaProgramElement addContext(StatementBlock pe) {
        final ContextInstantiationEntry cie = svInst.getContextInstantiation();
        if (cie == null) {
            throw new IllegalStateException("Context should also be instantiated");
        }

        if (cie.prefix() != null) {
            return ProgramContextAdder.INSTANCE.start(
                (JavaNonTerminalProgramElement) cie.contextProgram(), pe, cie.getInstantiation());
        }

        return pe;
    }

    private JavaBlock replacePrg(SVInstantiations svInst, JavaBlock jb) {
        if (svInst.isEmpty()) {
            return jb;
        }

        ProgramReplaceVisitor trans;
        ProgramElement result = null;

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

    private Term[] neededSubs(int n) {
        boolean newTerm = false;
        Term[] result = new Term[n];
        for (int i = n - 1; i >= 0; i--) {
            Object top = subStack.pop();
            if (top == newMarker) {
                newTerm = true;
                top = subStack.pop();
            }
            result[i] = (Term) top;
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
     * {@link ConstraintAwareSyntacticalReplaceVisitor} to recursively replace meta variables
     */
    protected Term toTerm(Term o) {
        return o;
    }


    private ElementaryUpdate instantiateElementaryUpdate(ElementaryUpdate op) {
        final UpdateableOperator originalLhs = op.lhs();
        if (originalLhs instanceof SchemaVariable) {
            Object lhsInst = svInst.getInstantiation((SchemaVariable) originalLhs);
            if (lhsInst instanceof Term) {
                lhsInst = ((Term) lhsInst).op();
            }

            final UpdateableOperator newLhs;
            if (lhsInst instanceof UpdateableOperator) {
                newLhs = (UpdateableOperator) lhsInst;
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


    private Operator instantiateOperatorSV(ModalOperatorSV op) {
        return (Operator) svInst.getInstantiation(op);
    }

    private Operator instantiateOperator(Operator p_operatorToBeInstantiated) {
        Operator instantiatedOp = p_operatorToBeInstantiated;
        if (p_operatorToBeInstantiated instanceof SortDependingFunction) {
            instantiatedOp =
                handleSortDependingSymbol((SortDependingFunction) p_operatorToBeInstantiated);
        } else if (p_operatorToBeInstantiated instanceof ElementaryUpdate) {
            instantiatedOp =
                instantiateElementaryUpdate((ElementaryUpdate) p_operatorToBeInstantiated);
        } else if (p_operatorToBeInstantiated instanceof ModalOperatorSV) {
            instantiatedOp = instantiateOperatorSV((ModalOperatorSV) p_operatorToBeInstantiated);
        } else if (p_operatorToBeInstantiated instanceof SchemaVariable) {
            if (p_operatorToBeInstantiated instanceof ProgramSV
                    && ((ProgramSV) p_operatorToBeInstantiated).isListSV()) {
                instantiatedOp = p_operatorToBeInstantiated;
            } else {
                instantiatedOp =
                    (Operator) svInst.getInstantiation((SchemaVariable) p_operatorToBeInstantiated);
            }
        }
        assert instantiatedOp != null;

        return instantiatedOp;
    }

    private ImmutableArray<QuantifiableVariable> instantiateBoundVariables(Term visited) {
        ImmutableArray<QuantifiableVariable> vBoundVars = visited.boundVars();
        if (!vBoundVars.isEmpty()) {
            final QuantifiableVariable[] newVars = new QuantifiableVariable[vBoundVars.size()];
            boolean varsChanged = false;

            for (int j = 0, size = vBoundVars.size(); j < size; j++) {
                QuantifiableVariable boundVar = vBoundVars.get(j);
                if (boundVar instanceof SchemaVariable) {
                    final SchemaVariable boundSchemaVariable = (SchemaVariable) boundVar;
                    final Term instantiationForBoundSchemaVariable =
                        (Term) svInst.getInstantiation(boundSchemaVariable);
                    if (instantiationForBoundSchemaVariable != null) {
                        boundVar = (QuantifiableVariable) instantiationForBoundSchemaVariable.op();
                    } else {
                        // this case may happen for PO generation of taclets
                        boundVar = (QuantifiableVariable) boundSchemaVariable;
                    }
                    varsChanged = true;
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
    public void visit(final Term visited) {
        // Sort equality has to be ensured before calling this method
        final Operator visitedOp = visited.op();
        if (visitedOp instanceof SchemaVariable && visitedOp.arity() == 0
                && svInst.isInstantiated((SchemaVariable) visitedOp)
                && (!(visitedOp instanceof ProgramSV && ((ProgramSV) visitedOp).isListSV()))) {
            final Term newTerm = toTerm(svInst.getTermInstantiation((SchemaVariable) visitedOp,
                svInst.getExecutionContext(), services));
            final Term labeledTerm = TermLabelManager.label(services, termLabelState,
                applicationPosInOccurrence, rule, ruleApp, goal, labelHint, visited, newTerm);
            pushNew(labeledTerm);
        } else {
            final Operator newOp = instantiateOperator(visitedOp);
            // instantiation of java block
            boolean jblockChanged = false;
            JavaBlock jb = visited.javaBlock();

            if (jb != JavaBlock.EMPTY_JAVABLOCK) {
                jb = replacePrg(svInst, jb);
                if (jb != visited.javaBlock()) {
                    jblockChanged = true;
                }
            }

            // instantiate bound variables
            final ImmutableArray<QuantifiableVariable> boundVars =
                instantiateBoundVariables(visited);

            // instantiate sub terms
            final Term[] neededsubs = neededSubs(newOp != null ? newOp.arity() : 0);
            if (boundVars != visited.boundVars() || jblockChanged || (newOp != visitedOp)
                    || (!subStack.empty() && subStack.peek() == newMarker)) {
                final ImmutableArray<TermLabel> labels = instantiateLabels(visited, newOp,
                    new ImmutableArray<>(neededsubs), boundVars, jb, visited.getLabels());
                final Term newTerm = tb.tf().createTerm(newOp, neededsubs, boundVars, jb, labels);
                pushNew(resolveSubst(newTerm));
            } else {
                Term t;
                final ImmutableArray<TermLabel> labels = instantiateLabels(visited, visitedOp,
                    visited.subs(), visited.boundVars(), visited.javaBlock(), visited.getLabels());
                if (!visited.hasLabels() && labels != null && labels.isEmpty()) {
                    t = visited;
                } else {
                    t = tb.tf().createTerm(visitedOp, visited.subs(), visited.boundVars(),
                        visited.javaBlock(), labels);
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

    private ImmutableArray<TermLabel> instantiateLabels(Term tacletTerm, Operator newTermOp,
            ImmutableArray<Term> newTermSubs, ImmutableArray<QuantifiableVariable> newTermBoundVars,
            JavaBlock newTermJavaBlock, ImmutableArray<TermLabel> newTermOriginalLabels) {
        return TermLabelManager.instantiateLabels(termLabelState, services,
            applicationPosInOccurrence, rule, ruleApp, goal, labelHint, tacletTerm, newTermOp,
            newTermSubs, newTermBoundVars, newTermJavaBlock, newTermOriginalLabels);
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

    private Term resolveSubst(Term t) {
        if (t.op() instanceof SubstOp) {
            Term resolved = ((SubstOp) t.op()).apply(t, tb);
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
    public Term getTerm() {
        if (computedResult == null) {
            Object o = null;
            do {
                o = subStack.pop();
            } while (o == newMarker);
            Term t = (Term) o;
            // CollisionDeletingSubstitutionTermApplier substVisit
            // = new CollisionDeletingSubstitutionTermApplier();
            // t.execPostOrder(substVisit);
            // t=substVisit.getTerm();
            computedResult = t;
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
        tacletTermStack.push(subtreeRoot);
        super.subtreeEntered(subtreeRoot);
    }

    /**
     * this method is called in execPreOrder and execPostOrder in class Term when leaving the
     * subtree rooted in the term subtreeRoot. Default implementation is to do nothing. Subclasses
     * can override this method when the visitor behaviour depends on informations bound to
     * subtrees.
     *
     * @param subtreeRoot root of the subtree which the visitor leaves.
     */
    @Override
    public void subtreeLeft(Term subtreeRoot) {
        tacletTermStack.pop();
        if (subtreeRoot.op() instanceof TermTransformer) {
            final TermTransformer mop = (TermTransformer) subtreeRoot.op();
            final Term newTerm = mop.transform((Term) subStack.pop(), svInst, services);
            final Term labeledTerm = TermLabelManager.label(services, termLabelState,
                applicationPosInOccurrence, rule, ruleApp, goal, labelHint, subtreeRoot, newTerm);
            pushNew(labeledTerm);
        }
    }
}
