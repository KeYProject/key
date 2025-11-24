/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Stack;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableArray;

/**
 * <p>
 * A lightweight version of {@link SyntacticalReplaceVisitor} which does not replace labels. This
 * saves a lot of dependencies to {@link Goal}, {@link RuleApp},
 * {@link org.key_project.prover.sequent.PosInOccurrence}
 * etc. and is therefore useful for internal computations not having access to all these objects.
 * Since labels
 * are not refactored, this class is *not* useful for rule applications etc.
 * </p>
 * <p>
 * Note that this class is basically a stripped-down copy of {@link SyntacticalReplaceVisitor}, so
 * problems in that class would carry over to this one...
 * </p>
 *
 * @author Dominic Steinhoefel
 */
public final class LightweightSyntacticalReplaceVisitor implements DefaultVisitor {
    private final SVInstantiations svInst;
    private final Services services;
    private final TermBuilder tb;
    private JTerm computedResult = null;

    /**
     * the stack contains the subterms that will be added in the next step of execPostOrder in Term
     * in order to build the new term. A boolean value between or under the subterms on the stack
     * indicate that a term using these subterms should build a new term instead of using the old
     * one, because one of its subterms has been built, too.
     */
    private final Stack<Object> subStack; // of Term (and Boolean)
    private final Boolean newMarker = Boolean.TRUE;

    /**
     * constructs a term visitor replacing any occurrence of a schemavariable found in
     * {@code svInst} by its instantiation
     *
     * @param svInst mapping of schemavariables to their instantiation
     * @param services the Services
     */
    public LightweightSyntacticalReplaceVisitor(SVInstantiations svInst, Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();
        this.svInst = svInst;
        subStack = new Stack<>(); // of Term
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
        if (jb.program() instanceof ContextStatementBlock csb) {
            trans = new ProgramReplaceVisitor(
                new StatementBlock(csb.getBody()), // TODO
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

    private void pushNew(Object t) {
        if (subStack.empty() || subStack.peek() != newMarker) {
            subStack.push(newMarker);
        }
        subStack.push(t);
    }

    private ElementaryUpdate instantiateElementaryUpdate(ElementaryUpdate op) {
        final UpdateableOperator originalLhs = op.lhs();
        if (originalLhs instanceof SchemaVariable originalLhsAsSV) {
            Object lhsInst = svInst.getInstantiation(originalLhsAsSV);
            if (lhsInst instanceof JTerm) {
                lhsInst = ((JTerm) lhsInst).op();
            }

            if (!(lhsInst instanceof final UpdateableOperator newLhs)) {
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
            instantiatedOp =
                handleSortDependingSymbol(sortDependingFunction);
        } else if (p_operatorToBeInstantiated instanceof ElementaryUpdate elementaryUpdate) {
            instantiatedOp = instantiateElementaryUpdate(elementaryUpdate);
        } else if (p_operatorToBeInstantiated instanceof JModality mod) {
            instantiatedOp = instantiateModality(mod, jb);
        } else if (p_operatorToBeInstantiated instanceof SchemaVariable sv) {
            if (!(p_operatorToBeInstantiated instanceof ProgramSV opSV && opSV.isListSV())) {
                instantiatedOp = (Operator) svInst.getInstantiation(sv);
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
                && (!(visitedOp instanceof ProgramSV visitedPSV && visitedPSV.isListSV()))) {
            final JTerm newTerm = svInst.getTermInstantiation(visitedSV,
                svInst.getExecutionContext(), services);
            pushNew(newTerm);
        } else {
            // instantiation of java block
            boolean jblockChanged = false;
            JavaBlock jb = JavaBlock.EMPTY_JAVABLOCK;
            if (visited.op() instanceof final JModality mod) {
                final JavaBlock originalBlock = mod.programBlock();
                jb = replacePrg(svInst, originalBlock);
                if (jb != originalBlock) {
                    jblockChanged = true;
                }
            }

            final Operator newOp = instantiateOperator(visitedOp, jb);

            // instantiate bound variables
            final ImmutableArray<QuantifiableVariable> boundVars = //
                instantiateBoundVariables(visited);

            // instantiate sub terms
            final JTerm[] neededsubs = neededSubs(newOp.arity());
            if (boundVars != visited.boundVars() || jblockChanged || (newOp != visitedOp)
                    || (!subStack.empty() && subStack.peek() == newMarker)) {
                final JTerm newTerm =
                    tb.tf().createTerm(newOp, neededsubs, boundVars, visited.getLabels());
                pushNew(resolveSubst(newTerm));
            } else {
                JTerm term = resolveSubst(visited);
                if (term == visited) {
                    subStack.push(visited);
                } else {
                    pushNew(visited);
                }
            }
        }
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
        if (t.op() instanceof SubstOp substOp) {
            final JTerm resolved = substOp.apply(t, tb);
            return tb.label(resolved, t.sub(1).getLabels());
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
            computedResult = (JTerm) o;
        }
        return computedResult;
    }

    public SVInstantiations getSVInstantiations() {
        return svInst;
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
        if (subtreeRoot.op() instanceof TermTransformer mop) {
            final JTerm newTerm = //
                mop.transform((JTerm) subStack.pop(), svInst, services);
            pushNew(newTerm);
        }
    }
}
