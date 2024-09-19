/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import java.util.Stack;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.LogicVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.UpdateSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

import static org.key_project.rusty.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * This variable condition can be used to check whether an update can be performed on a formula or
 * term.
 * That is the case if the top-level operator is rigid and of arity greater than 0.
 *
 * @author Benjamin Weiss
 * @author Tobias Reinhold
 */
public final class ApplyUpdateOnRigidCondition implements VariableCondition {

    /**
     * The schema variable matched against an update
     */
    private final UpdateSV u;

    /**
     * The schema variable matched against a formula or term
     */
    private final SchemaVariable phi;

    /**
     * The schema variable containing the result of applying the update <code>u</code> on the
     * formula or term <code>phi</code>
     */
    private final SchemaVariable result;

    /**
     * Creates an instance of the variable condition.
     *
     * @param u the schema variable matched against an update
     * @param phi the schema variable matched against a formula or term
     * @param result the schema variable containing the result of applying <code>u</code> on
     *        <code>phi</code>
     */
    public ApplyUpdateOnRigidCondition(UpdateSV u, SchemaVariable phi, SchemaVariable result) {
        this.u = u;
        this.phi = phi;
        this.result = result;
    }

    /**
     * <p>
     * Applies the update <code>u</code> on the rigid formula or term <code>phi</code>.
     * </p>
     * If there are free variables in <code>u</code>,
     * {@link #applyUpdateOnRigidQuantifier(Term, Term, Services)} is
     * called to take care of potential name clashes.
     *
     * @param u the update applied on <code>phi</code>
     * @param phi the formula or term the update <code>u</code> is applied on
     * @param services the {@link Services} to help create terms
     * @return the term of the update <code>u</code> applied on all subterms of <code>phi</code> and
     *         possible renaming
     */
    private static Term applyUpdateOnRigid(Term u, Term phi, Services services) {
        if (phi.boundVars().isEmpty() || u.freeVars().isEmpty()) {
            final TermBuilder tb = services.getTermBuilder();
            final Term[] updatedSubs = new Term[phi.arity()];
            for (int i = 0; i < updatedSubs.length; i++) {
                updatedSubs[i] = tb.apply(u, phi.sub(i));
            }

            return services.getTermFactory().createTerm(phi.op(), updatedSubs,
                (ImmutableArray<QuantifiableVariable>) phi.boundVars());
        }

        // Here we have to check for name collisions as there are free variables in u
        return applyUpdateOnRigidQuantifier(u, phi, services);
    }

    /**
     * <p>
     * This method is used by {@link #applyUpdateOnRigid(Term, Term, Services)} if {@code phi} is a
     * quantifier and
     * {@code u} contains free variables.
     * </p>
     *
     * @param u the update applied on <code>phi</code>
     * @param phi the formula or term the update <code>u</code> is applied on
     * @param services the {@link Services} to help create terms
     * @return the term of the update <code>u</code> applied on all subterms of <code>phi</code> and
     *         possible renaming
     */
    private static Term applyUpdateOnRigidQuantifier(Term u, Term phi, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term[] updatedSubs = phi.subs().toArray(new Term[0]);

        for (int i = 0; i < updatedSubs.length; i++) {
            updatedSubs[i] = tb.apply(u, updatedSubs[i]);
        }

        u.execPostOrder(new Visitor<@NonNull Term>() {
            /**
             * the stack contains the subterms that will be added in the next step of execPostOrder
             * in Term
             * in order to build the new term. A boolean value between or under the subterms on the
             * stack
             * indicate that a term using these subterms should build a new term instead of using
             * the old
             * one, because one of its subterms has been built, too.
             */
            private final Stack<Object> subStack = new Stack<>(); // of Term (and Boolean)
            private final Boolean newMarker = Boolean.TRUE;

            @Override
            public void visit(Term visited) {
                Operator visitedOp = visited.op();
                if (visitedOp instanceof LogicVariable lv) {
                    pushNew(new LogicVariable(lv.getIndex() + 1, lv.sort()));
                }
                // instantiate sub terms
                final Term[] neededSubs = neededSubs(visitedOp.arity());
                if (!subStack.empty() && subStack.peek() == newMarker) {
                    final Term newTerm = tb.tf().createTerm(visitedOp, neededSubs,
                        (ImmutableArray<QuantifiableVariable>) visited.boundVars());
                    pushNew(newTerm);
                } else {
                    subStack.push(visited);
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

            void pushNew(Object t) {
                if (subStack.empty() || subStack.peek() != newMarker) {
                    subStack.push(newMarker);
                }
                subStack.push(t);
            }
        });

        return services.getTermFactory().createTerm(phi.op(), updatedSubs,
            (ImmutableArray<QuantifiableVariable>) phi.boundVars());
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions mc,
            Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term uInst = (Term) svInst.getInstantiation(u);
        Term phiInst = (Term) svInst.getInstantiation(phi);
        Term resultInst = (Term) svInst.getInstantiation(result);
        if (uInst == null || phiInst == null) {
            return mc;
        }

        if (!phiInst.op().isRigid() || phiInst.op().arity() == 0) {
            return null;
        }
        Term properResultInst = applyUpdateOnRigid(uInst, phiInst, services);
        if (resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return mc.setInstantiations(svInst);
        } else if (RENAMING_TERM_PROPERTY.equalsModThisProperty(resultInst, properResultInst)) {
            return mc;
        } else {
            return null;
        }
    }


    @Override
    public String toString() {
        return "\\applyUpdateOnRigid(" + u + ", " + phi + ", " + result + ")";
    }
}
