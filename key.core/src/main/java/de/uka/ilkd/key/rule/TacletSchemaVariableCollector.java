/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.java.visitor.ProgramSVCollector;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;


/**
 * Collects all schemavariables occurring in the <code>\find, \assumes</code> part or goal
 * description of a taclet. The addrule section is scanned optionally.
 *
 * Duplicates are not removed because the use of persistent datastructure and up to now we just have
 * a SetAsList-implementaion causing to have O(sqr(n)) if it would used.
 *
 * For example, {@link TacletApp} uses this class to determine all
 * uninstantiated schemavariables.
 */
public class TacletSchemaVariableCollector implements DefaultVisitor {

    /** collects all found variables */
    protected @NonNull ImmutableList<SchemaVariable> varList;
    /** the instantiations needed for unwind loop constructs */
    private @NonNull SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;


    public TacletSchemaVariableCollector() {
        varList = ImmutableSLList.nil();
    }


    /**
     * @param svInsts the SVInstantiations that have been already found (needed by unwind loop
     *        constructs to determine which labels are needed)
     */
    public TacletSchemaVariableCollector(@NonNull SVInstantiations svInsts) {
        varList = ImmutableSLList.nil();
        instantiations = svInsts;
    }


    /**
     * collects all SchemVariables that occur in the JavaBlock
     *
     * @param jb the JavaBlock where to look for Schemavariables
     * @param vars the IList<SchemaVariable> where to add the found SchemaVariables
     * @return the extended list of found schemavariables
     */
    protected ImmutableList<SchemaVariable> collectSVInProgram(@NonNull JavaBlock jb,
            @NonNull ImmutableList<SchemaVariable> vars) {

        ProgramSVCollector prgSVColl = new ProgramSVCollector(jb.program(), vars, instantiations);
        prgSVColl.start();
        return prgSVColl.getSchemaVariables();
    }


    /**
     * visits the Term in post order {@link Term#execPostOrder(org.key_project.logic.Visitor)} and
     * collects all found
     * schema variables
     *
     * @param p_visited the Term whose schema variables are collected
     */
    @Override
    public void visit(@NonNull Term p_visited) {
        final var visited = (JTerm) p_visited;
        final Operator op = visited.op();
        if (op instanceof JModality mod) {
            if (mod.kind() instanceof ModalOperatorSV msv) {
                varList = varList.prepend(msv);
            }
            varList = collectSVInProgram(mod.programBlock(), varList);
        } else if (op instanceof ElementaryUpdate) {
            varList = collectSVInElementaryUpdate((ElementaryUpdate) op, varList);
        }

        for (int j = 0, ar = visited.arity(); j < ar; j++) {
            for (int i = 0, sz = visited.varsBoundHere(j).size(); i < sz; i++) {
                final QuantifiableVariable qVar = visited.varsBoundHere(j).get(i);
                if (qVar instanceof SchemaVariable) {
                    varList = varList.prepend((SchemaVariable) qVar);
                }
            }
        }

        if (op instanceof SchemaVariable) {
            varList = varList.prepend((SchemaVariable) op);
        }

        for (TermLabel label : ((JTerm) visited).getLabels()) {
            if (label instanceof TermLabelSV) {
                varList = varList.prepend((SchemaVariable) label);
            }
        }
    }


    /**
     * collects all schema variables occurring on the lhs of an elementary update
     *
     * @param op the ElementaryUpdate operator to be scanned for schemavariables
     * @param vars the ImmutableList<SchemaVariable> with already found schema variables
     * @return a list of schema variables containing the ones of <code>vars</code> together with the
     *         schema variables found in <code>op</code>
     */
    private ImmutableList<SchemaVariable> collectSVInElementaryUpdate(
            @NonNull ElementaryUpdate op,
            @NonNull ImmutableList<SchemaVariable> vars) {
        ImmutableList<SchemaVariable> result = vars;

        if (op.lhs() instanceof SchemaVariable) {
            result = result.prepend((SchemaVariable) op.lhs());
        }

        return result;
    }

    /** @return list of found Variables */
    public Iterable<SchemaVariable> vars() {
        return varList;
    }

    /** @return iterator of the found Variables */
    public Iterator<SchemaVariable> varIterator() {
        return varList.iterator();
    }


    /** @return number of the found variables */
    public int size() {
        return varList.size();
    }


    /** @return true iff term contains the given variable */
    public boolean contains(SchemaVariable var) {
        return varList.contains(var);
    }


    /**
     * collects all variables in a Semisequent
     *
     * @param semiseq the Semisequent to visit
     */
    private void visit(@NonNull Semisequent semiseq) {
        for (final SequentFormula aSemiseq : semiseq) {
            aSemiseq.formula().execPostOrder(this);
        }
    }


    /**
     * goes through the given sequent an collects all vars found
     *
     * @param seq the Sequent to visit
     */
    public void visit(@NonNull Sequent seq) {
        visit(seq.antecedent());
        visit(seq.succedent());
    }

    /**
     * collects all schema variables of a taclet
     *
     * @param taclet the Taclet where the variables have to be collected to
     * @param visitAddrules a boolean that contols if the addrule sections are to be ignored (iff
     *        false) or if the visitor descends into them (iff true)
     */
    public void visit(@NonNull Taclet taclet,
            boolean visitAddrules) {
        visit(taclet.assumesSequent());
        visitFindPart(taclet);
        visitGoalTemplates(taclet, visitAddrules);
    }


    protected void visitFindPart(@NonNull Taclet taclet) {
        if (taclet instanceof FindTaclet) {
            (((FindTaclet) taclet).find()).execPostOrder(this);
        }
    }


    protected void visitGoalTemplates(@NonNull Taclet taclet, boolean visitAddrules) {
        for (var tacletGoalTemplate : taclet.goalTemplates()) {
            var gt = tacletGoalTemplate;
            visit(gt.sequent());
            if (gt instanceof RewriteTacletGoalTemplate) {
                ((RewriteTacletGoalTemplate) gt).replaceWith().execPostOrder(this);
            } else {
                if (gt instanceof AntecSuccTacletGoalTemplate) {
                    visit(((AntecSuccTacletGoalTemplate) gt).replaceWith());
                }
            }
            if (visitAddrules) {
                for (var addRulesTaclet : gt.rules()) {
                    visit(addRulesTaclet, true);
                }
            }
        }
    }


    /**
     * collects all variables in a Taclet but ignores the variables that appear only in the addrule
     * sections of the Taclet
     *
     * @param taclet the Taclet where the variables have to be collected to
     */
    public void visitWithoutAddrule(@NonNull Taclet taclet) {
        visit(taclet, false);
    }

}
