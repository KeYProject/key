/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.tacletbuilder;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// This class contains the goal of a taclet. There are new
/// sequents that have to be added, new rules and rule variables.
/// The replacewith-goal is implemented in subclasses
public abstract class TacletGoalTemplate {
    /// stores sequent that is one of the new goals
    protected final Sequent addedSeq;

    /// stores list of Taclet which are introduced
    protected final ImmutableList<? extends Taclet> addedRules;

    /// program variables added by this taclet to the namespace
    protected final ImmutableSet<SchemaVariable> addedProgVars;

    private @Nullable String name;

    /// Creates a new goal template for a taclet
    ///
    /// @param addedSeq new Sequent to be added
    /// @param addedRules IList<Taclet> contains the new allowed rules at this branch
    /// @param addedProgVars a SetOf<SchemaVariable> which will be instantiated with an application
    /// time unused (new) program variables that are introduced by an application of this
    /// template
    protected TacletGoalTemplate(Sequent addedSeq,
            @NonNull ImmutableList<? extends Taclet> addedRules,
            @NonNull ImmutableSet<SchemaVariable> addedProgVars) {
        // TacletBuilder.checkContainsFreeVarSV(addedSeq, null, "add sequent");

        this.addedRules = addedRules;
        this.addedSeq = addedSeq;
        this.addedProgVars = addedProgVars;
    }

    /// creates new Goaldescription same effect as <code>new TacletGoalTemplate(addedSeq,
    /// addedRules,
    /// SetAsListOf.<SchemaVariable>nil())
    /// </code>
    ///
    /// @param addedSeq new Sequent to be added
    /// @param addedRules IList<Taclet> contains the new allowed rules at this branch
    protected TacletGoalTemplate(Sequent addedSeq, ImmutableList<Taclet> addedRules) {
        this(addedSeq, addedRules, DefaultImmutableSet.nil());
    }

    /// a Taclet may add a new Sequent as Goal. Use this method to get this Sequent
    ///
    /// @return Sequent to be added as Goal or Sequent.EMPTY_SEQUENT if no such Sequent exists
    public Sequent sequent() {
        return addedSeq;
    }

    /// the goal of a Taclet may introduce new rules. Call this method to get them
    ///
    /// @return IList<Taclet> contains new introduced rules
    public ImmutableList<? extends Taclet> rules() {
        return addedRules;
    }

    public ImmutableSet<SchemaVariable> addedProgVars() {
        return addedProgVars;
    }

    public @Nullable Object replaceWithExpressionAsObject() {
        return null;
    }

    /// retrieves and returns all variables that are bound in the goal template
    ///
    /// @return all variables that occur bound in this goal template
    public abstract ImmutableSet<QuantifiableVariable> getBoundVariables();

    public void setName(@Nullable String name) {
        this.name = name;
    }

    public @Nullable String name() {
        return name;
    }


    @Override
    public boolean equals(@Nullable Object o) {

        if (o == null) {
            return false;
        }
        if (o == this) {
            return true;
        }

        if (getClass() != o.getClass()) {
            return false;
        }

        TacletGoalTemplate other = (TacletGoalTemplate) o;

        return addedSeq.equals(other.addedSeq) && addedRules.equals(other.addedRules);
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + addedSeq.hashCode();
        result = 37 * result + addedRules.hashCode();
        return result;
    }

    @Override
    public String toString() {
        String result = "";
        if (!sequent().isEmpty()) {
            result += "\\add " + sequent() + " ";
        }
        if (!rules().isEmpty()) {
            result += "\\addrules " + rules() + " ";
        }
        if (!addedProgVars().isEmpty()) {
            result += "\\addprogvars " + addedProgVars() + " ";
        }
        return result;
    }
}
