/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * this class inherits from TacletGoalTemplate. It is used if there is a replacewith in the
 * ruleGoals that replaces a sequent with a sequent. The replacewith for terms/formulae is realized
 * in another class calles RewriteTacletGoalTemplate.
 */
public class AntecSuccTacletGoalTemplate extends TacletGoalTemplate {
    /** sequent that replaces another one */
    private Sequent replacewith = Sequent.EMPTY_SEQUENT;

    /**
     * creates new Goaldescription
     *
     * @param addedSeq new Sequent to be added
     * @param addedRules IList<Taclet> contains the new allowed rules at this branch
     * @param replacewith the Sequent that replaces another one
     */
    public AntecSuccTacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules,
            Sequent replacewith, ImmutableSet<SchemaVariable> pvs) {
        super(addedSeq, addedRules, pvs);
        TacletBuilder.checkContainsFreeVarSV(replacewith, null, "replacewith sequent");
        this.replacewith = replacewith;
    }

    public AntecSuccTacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules,
            Sequent replacewith) {
        this(addedSeq, addedRules, replacewith, DefaultImmutableSet.nil());
    }

    /**
     * a Taclet may replace a Sequent by another. The new Sequent is returned. this Sequent.
     *
     * @return Sequent being paramter in the rule goal replacewith(Seq)
     */
    public Sequent replaceWith() {
        return replacewith;
    }

    /**
     * rertieves and returns all variables that are bound in the goal template
     *
     * @return all variables that occur bound in this goal template
     */
    @Override
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(replaceWith());
        return bvv.getBoundVariables().union(super.getBoundVariables());
    }

    /**
     * @return Sequent being paramter in the rule goal replacewith(Seq)
     */
    @Override
    public Object replaceWithExpressionAsObject() {
        return replacewith;
    }


    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }
        final AntecSuccTacletGoalTemplate other = (AntecSuccTacletGoalTemplate) o;
        return replacewith.equals(other.replacewith);
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + super.hashCode();
        result = 37 * result + replacewith.hashCode();
        return result;
    }


    /** toString */
    @Override
    public String toString() {
        String result = super.toString();
        result += "\\replacewith(" + replaceWith() + ") ";
        return result;
    }

}
