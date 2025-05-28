/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.rusty.ast.visitor.ProgramSVCollector;
import org.key_project.rusty.logic.RustyBlock;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ModalOperatorSV;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.rusty.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import org.key_project.rusty.rule.tacletbuilder.RewriteTacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class TacletSchemaVariableCollector implements Visitor<@NonNull Term> {
    /** collects all found variables */
    protected ImmutableList<SchemaVariable> varList;
    /** the instantiations needed for unwind loop constructs */
    private SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    public TacletSchemaVariableCollector() {
        varList = ImmutableSLList.nil();
    }


    /**
     * @param svInsts the SVInstantiations that have been already found (needed by unwind loop
     *        constructs to determine which labels are needed)
     */
    public TacletSchemaVariableCollector(SVInstantiations svInsts) {
        varList = ImmutableSLList.nil();
        instantiations = svInsts;
    }


    /**
     * collects all SchemVariables that occur in the RustBlock
     *
     * @param rb the RustBlock where to look for Schemavariables
     * @param vars the IList<SchemaVariable> where to add the found SchemaVariables
     * @return the extended list of found schemavariables
     */
    protected ImmutableList<SchemaVariable> collectSVInProgram(RustyBlock rb,
            ImmutableList<SchemaVariable> vars) {
        ProgramSVCollector prgSVColl = new ProgramSVCollector(rb.program(), vars, instantiations);
        prgSVColl.start();
        return prgSVColl.getSchemaVariables();
    }


    /**
     * visits the Term in post order {@link Term#execPostOrder(org.key_project.logic.Visitor)} and
     * collects all found
     * schema variables
     *
     * @param visited the Term whose schema variables are collected
     */
    @Override
    public void visit(Term visited) {
        final Operator op = visited.op();
        if (op instanceof Modality mod) {
            if (mod.kind() instanceof ModalOperatorSV msv) {
                varList = varList.prepend(msv);
            }
            varList = collectSVInProgram(mod.program(), varList);
        } else if (op instanceof ElementaryUpdate eu) {
            varList = collectSVInElementaryUpdate(eu, varList);
        }

        for (int j = 0, ar = visited.arity(); j < ar; j++) {
            for (int i = 0, sz = visited.varsBoundHere(j).size(); i < sz; i++) {
                final QuantifiableVariable qVar = visited.varsBoundHere(j).get(i);
                if (qVar instanceof SchemaVariable sv) {
                    varList = varList.prepend(sv);
                }
            }
        }

        if (op instanceof SchemaVariable) {
            varList = varList.prepend((SchemaVariable) op);
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
    private ImmutableList<SchemaVariable> collectSVInElementaryUpdate(ElementaryUpdate op,
            ImmutableList<SchemaVariable> vars) {
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
    private void visit(Semisequent semiseq) {
        for (var aSemiseq : semiseq) {
            aSemiseq.formula().execPostOrder(this);
        }
    }


    /**
     * goes through the given sequent a collects all vars found
     *
     * @param seq the Sequent to visit
     */
    public void visit(org.key_project.prover.sequent.Sequent seq) {
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
    public void visit(Taclet taclet, boolean visitAddrules) {
        visit(taclet.assumesSequent());
        visitFindPart(taclet);
        visitGoalTemplates(taclet, visitAddrules);
    }


    protected void visitFindPart(Taclet taclet) {
        if (taclet instanceof FindTaclet) {
            (((FindTaclet) taclet).find()).execPostOrder(this);
        }
    }


    protected void visitGoalTemplates(Taclet taclet, boolean visitAddrules) {
        for (var tacletGoalTemplate : taclet.goalTemplates()) {
            visit(tacletGoalTemplate.sequent());
            if (tacletGoalTemplate instanceof RewriteTacletGoalTemplate rt) {
                rt.replaceWith().execPostOrder(this);
            } else {
                if (tacletGoalTemplate instanceof AntecSuccTacletGoalTemplate ast) {
                    visit(ast.replaceWith());
                }
            }
            if (visitAddrules) {
                for (var taclet1 : tacletGoalTemplate.rules()) {
                    visit((Taclet) taclet1, true);
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
    public void visitWithoutAddrule(Taclet taclet) {
        visit(taclet, false);
    }
}
