/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Stack;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.UpdateableOperator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.expr.ContextBlockExpression;
import org.key_project.rusty.ast.visitor.ProgramContextAdder;
import org.key_project.rusty.ast.visitor.ProgramReplaceVisitor;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.SubstOp;
import org.key_project.rusty.logic.op.TermTransformer;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.inst.ContextInstantiationEntry;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableArray;

/**
 * A lightweight version of {@link SyntacticalReplaceVisitor} which does not replace labels. This
 * saves a lot of dependencies to {@link Goal}, {@link RuleApp}, {@link PosInOccurrence} etc. and is
 * therefore useful for internal computations not having access to all these objects. Since labels
 * are not refactored, this class is *not* useful for rule applications etc.
 *
 * Note that this class is basically a stripped-down copy of {@link SyntacticalReplaceVisitor}, so
 * problems in that class would carry over to this one...
 *
 * @author Dominic Steinhoefel
 */
public class LightweightSyntacticalReplaceVisitor implements Visitor<Term> {
    private final SVInstantiations svInst;
    private final Services services;
    private final TermBuilder tb;
    private Term computedResult = null;

    /**
     * the stack contains the subterms that will be added in the next step of execPostOrder in Term
     * in order to build the new term. A boolean value between or under the subterms on the stack
     * indicate that a term using these subterms should build a new term instead of using the old
     * one, because one of its subterms has been built, too.
     */
    private final Stack<Object> subStack; // of Term (and Boolean)
    private final Boolean newMarker = Boolean.TRUE;
    private final Deque<Term> tacletTermStack = new ArrayDeque<>();

    public LightweightSyntacticalReplaceVisitor(SVInstantiations svInst, Services services) {
        this.svInst = svInst;
        this.services = services;
        this.tb = services.getTermBuilder();
        subStack = new Stack<>(); // of Term
    }

    public LightweightSyntacticalReplaceVisitor(Services services) {
        this(SVInstantiations.EMPTY_SVINSTANTIATIONS, services);
    }

    private RustyProgramElement addContext(BlockExpression be) {
        final ContextInstantiationEntry cie = svInst.getContextInstantiation();
        if (cie == null) {
            throw new IllegalStateException("Context should also be instantiated");
        }

        if (cie.prefix() != null) {
            return ProgramContextAdder.INSTANCE.start(cie.contextProgram(),
                (ContextBlockExpression) be, cie.getInstantiation());
        }

        return be;
    }

    /**
     * the method is only still invoked to allow the
     * {@link ConstraintAwareSyntacticalReplaceVisitor} to recursively replace meta variables
     */
    protected Term toTerm(Term o) {
        return o;
    }

    @Override
    public void visit(Term visited) {
        // Sort equality has to be ensured before calling this method
        Operator visitedOp = visited.op();
        if (visitedOp instanceof SchemaVariable visitedSV && visitedOp.arity() == 0
                && svInst.isInstantiated(visitedSV)
                && (!(visitedOp instanceof ProgramSV visitedPSV && visitedPSV.isListSV()))) {
            final Term newTerm = toTerm(svInst.getTermInstantiation(visitedSV,
                services));
            pushNew(newTerm);
        } else {
            // instantiation of java block
            boolean rblockChanged = false;

            if (visitedOp instanceof Modality mod) {
                var rb = mod.program();
                var olfRb = rb;
                rb = replacePrg(svInst, rb);
                if (rb != olfRb) {
                    rblockChanged = true;
                }

                visitedOp = instantiateModality(mod, rb);
            }

            final Operator newOp = instantiateOperator(visitedOp);

            // instantiate bound variables
            final var boundVars = //
                instantiateBoundVariables(visited);

            // instantiate sub terms
            final Term[] neededsubs = neededSubs(newOp.arity());
            if (boundVars != visited.boundVars() || rblockChanged || (newOp != visitedOp)
                    || (!subStack.empty() && subStack.peek() == newMarker)) {
                final Term newTerm =
                    tb.tf().createTerm(newOp, neededsubs,
                        (ImmutableArray<QuantifiableVariable>) boundVars);
                pushNew(resolveSubst(newTerm));
            } else {
                Term term = resolveSubst(visited);
                if (term == visited) {
                    subStack.push(visited);
                } else {
                    pushNew(visited);
                }
            }
        }
    }

    private ImmutableArray<? extends QuantifiableVariable> instantiateBoundVariables(Term visited) {
        var vBoundVars = visited.boundVars();
        if (!vBoundVars.isEmpty()) {
            final QuantifiableVariable[] newVars = new QuantifiableVariable[vBoundVars.size()];
            boolean varsChanged = false;

            for (int j = 0, size = vBoundVars.size(); j < size; j++) {
                QuantifiableVariable boundVar = vBoundVars.get(j);
                if (boundVar instanceof SchemaVariable boundSchemaVariable) {
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

    protected Operator instantiateOperator(Operator p_operatorToBeInstantiated) {
        Operator instantiatedOp = p_operatorToBeInstantiated;
        /*
         * if (p_operatorToBeInstantiated instanceof SortDependingFunction) {
         * instantiatedOp =
         * handleSortDependingSymbol((SortDependingFunction) p_operatorToBeInstantiated);
         * } else
         */
        if (p_operatorToBeInstantiated instanceof ElementaryUpdate eu) {
            instantiatedOp =
                instantiateElementaryUpdate(eu);
        } else if (p_operatorToBeInstantiated instanceof SchemaVariable sv) {
            if (sv instanceof ProgramSV opSV && opSV.isListSV()) {
                instantiatedOp = p_operatorToBeInstantiated;
            } else {
                instantiatedOp = (Operator) svInst.getInstantiation(sv);
            }
        }
        assert instantiatedOp != null;

        return instantiatedOp;
    }

    private ElementaryUpdate instantiateElementaryUpdate(ElementaryUpdate op) {
        final UpdateableOperator originalLhs = op.lhs();
        if (originalLhs instanceof SchemaVariable originalLhsAsSV) {
            Object lhsInst = svInst.getInstantiation(originalLhsAsSV);
            if (lhsInst instanceof Term) {
                lhsInst = ((Term) lhsInst).op();
            }

            final UpdateableOperator newLhs;
            if (lhsInst instanceof UpdateableOperator uo) {
                newLhs = uo;
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

    private RustyBlock replacePrg(SVInstantiations svInst, RustyBlock rb) {
        if (svInst.isEmpty()) {
            return rb;
        }

        ProgramReplaceVisitor trans;
        RustyProgramElement result = null;

        if (rb.program() instanceof ContextBlockExpression cbe) {
            trans = new ProgramReplaceVisitor(
                cbe,
                services, svInst);
            trans.start();
            result = addContext((ContextBlockExpression) trans.result());
        } else {
            trans = new ProgramReplaceVisitor(rb.program(), services, svInst);
            trans.start();
            result = trans.result();
        }
        return (result == rb.program()) ? rb : new RustyBlock(result);
    }

    private Operator instantiateModality(Modality op, RustyBlock rb) {
        Modality.RustyModalityKind kind = op.kind();
        if (op.kind() instanceof ModalOperatorSV) {
            kind = (Modality.RustyModalityKind) svInst.getInstantiation(op.kind());
        }
        if (rb != op.program() || kind != op.kind()) {
            return Modality.getModality(kind, rb);
        }
        return op;
    }

    private Term resolveSubst(Term t) {
        if (t.op() instanceof SubstOp so) {
            Term resolved = so.apply(t, tb);
            return resolved;
        } else {
            return t;
        }
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
     * delivers the new built term
     */
    public Term getTerm() {
        if (computedResult == null) {
            Object o = null;
            do {
                o = subStack.pop();
            } while (o == newMarker);
            computedResult = (Term) o;
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
        if (subtreeRoot.op() instanceof TermTransformer mop) {
            final Term newTerm = //
                mop.transform((Term) subStack.pop(), svInst, services);
            pushNew(newTerm);
        }
    }
}
