/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.SubstOp;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

/**
 * This visitor is used to collect information about schema variable pairs occurring within the same
 * substitution operator within a taclet. This information is used to choose names of metavariables
 * or skolem functions.
 */

public class SVNameCorrespondenceCollector implements DefaultVisitor {

    /**
     * This map contains (a, b) if there is a substitution {b a} somewhere in the taclet
     */
    private ImmutableMap<SchemaVariable, SchemaVariable> nameCorrespondences =
        DefaultImmutableMap.nilMap();

    private final HeapLDT heapLDT;


    SVNameCorrespondenceCollector(HeapLDT heapLDT) {
        this.heapLDT = heapLDT;
    }


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


    private void addNameCorrespondence(SchemaVariable nameReceiver, SchemaVariable nameProvider) {
        nameCorrespondences = nameCorrespondences.put(nameReceiver, nameProvider);
    }


    /**
     * @return the found correspondences as a map, mapping schema variable a onto schema variables b
     *         if b is replaced with a somewhere in this taclet
     */
    public ImmutableMap<SchemaVariable, SchemaVariable> getCorrespondences() {
        return nameCorrespondences;
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
        visit(taclet.assumesSequent());
        if (taclet instanceof FindTaclet) {
            final Term findTerm = ((FindTaclet) taclet).find();
            findTerm.execPostOrder(this);
            if (findTerm.op() instanceof SchemaVariable) {
                findSV = (SchemaVariable) findTerm.op();
            } else if (findTerm.op() instanceof Function
                    && heapLDT.containsFunction((Function) findTerm.op())) {
                findSV = (SchemaVariable) findTerm.sub(2).op();
            }
        }
        for (var gt : taclet.goalTemplates()) {
            visit(gt.sequent());
            if (gt instanceof RewriteTacletGoalTemplate) {
                final JTerm replaceWithTerm = ((RewriteTacletGoalTemplate) gt).replaceWith();
                replaceWithTerm.execPostOrder(this);
                if (findSV != null && replaceWithTerm.op() instanceof SchemaVariable) {
                    addNameCorrespondence((SchemaVariable) replaceWithTerm.op(), findSV);
                }
            } else {
                if (gt instanceof AntecSuccTacletGoalTemplate) {
                    visit(((AntecSuccTacletGoalTemplate) gt).replaceWith());
                }
            }
            if (visitAddrules) {
                for (var taclet1 : gt.rules()) {
                    visit((Taclet) taclet1, true);
                }
            }
        }
    }


}
