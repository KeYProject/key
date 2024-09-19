/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.rusty.logic.Semisequent;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.logic.op.SubstOp;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import org.key_project.rusty.rule.tacletbuilder.RewriteTacletGoalTemplate;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

import org.jspecify.annotations.NonNull;

/**
 * This visitor is used to collect information about schema variable pairs occurring within the same
 * substitution operator within a taclet. This information is used to choose names of metavariables
 * or skolem functions.
 */
public class SVNameCorrespondenceCollector implements Visitor<@NonNull Term> {
    /**
     * This map contains (a, b) if there is a substitution {b a} somewhere in the taclet
     */
    private ImmutableMap<SchemaVariable, SchemaVariable> nameCorrespondences =
        DefaultImmutableMap.nilMap();

    /**
     * is called by the execPostOrder-method of a term
     *
     * @param t the Term if the toplevel operator of this term is a substitution of schema
     *        variables, then this pair is added to the map "nameCorrespondences"
     */
    public void visit(Term t) {
        final var top = t.op();
        if (top instanceof SubstOp) {
            final var substTermOp = t.sub(0).op();
            final var substVar = t.varsBoundHere(1).get(0);
            if (substTermOp instanceof SchemaVariable substTermSV
                    && substVar instanceof SchemaVariable substVarSV) {
                addNameCorrespondence(substTermSV, substVarSV);
            }
        }
    }

    /**
     * @return the found correspondences as a map, mapping schema variable a onto schema variables b
     *         if b is replaced with a somewhere in this taclet
     */
    public ImmutableMap<SchemaVariable, SchemaVariable> getCorrespondences() {
        return nameCorrespondences;
    }

    private void addNameCorrespondence(SchemaVariable nameReceiver, SchemaVariable nameProvider) {
        nameCorrespondences = nameCorrespondences.put(nameReceiver, nameProvider);
    }

    /**
     * collects all correspondences in a semisequent
     *
     * @param semiseq the Semisequent to visit
     */
    private void visit(Semisequent semiseq) {
        for (SequentFormula cf : semiseq) {
            cf.formula().execPostOrder(this);
        }
    }

    /**
     * collects all correspondences in a sequent
     *
     * @param seq the Sequent to visit
     */
    public void visit(Sequent seq) {
        visit(seq.antecedent());
        visit(seq.succedent());
    }

    /**
     * collects all correspondences in a taclet
     *
     * @param taclet the Taclet where the correspondences have to be collected
     * @param visitAddrules a boolean that contols if the addrule sections are to be ignored (iff
     *        false) or if the visitor descends into them (iff true)
     */
    public void visit(Taclet taclet, boolean visitAddrules) {
        SchemaVariable findSV = null;
        visit(taclet.ifSequent());
        if (taclet instanceof FindTaclet) {
            final Term findTerm = ((FindTaclet) taclet).find();
            findTerm.execPostOrder(this);
            if (findTerm.op() instanceof SchemaVariable sv) {
                findSV = sv;
            }
        }
        for (TacletGoalTemplate tacletGoalTemplate : taclet.goalTemplates()) {
            TacletGoalTemplate gt = tacletGoalTemplate;
            visit(gt.sequent());
            if (gt instanceof RewriteTacletGoalTemplate rwtgt) {
                final Term replaceWithTerm = rwtgt.replaceWith();
                replaceWithTerm.execPostOrder(this);
                if (findSV != null && replaceWithTerm.op() instanceof SchemaVariable sv) {
                    addNameCorrespondence(sv, findSV);
                }
            } else {
                if (gt instanceof AntecSuccTacletGoalTemplate astgt) {
                    visit(astgt.replaceWith());
                }
            }
            if (visitAddrules) {
                for (Taclet taclet1 : gt.rules()) {
                    visit(taclet1, true);
                }
            }
        }
    }
}
