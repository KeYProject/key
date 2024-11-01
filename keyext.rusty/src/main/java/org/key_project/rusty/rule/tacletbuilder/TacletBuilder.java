/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.tacletbuilder;

import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.logic.op.sv.VariableSV;
import org.key_project.rusty.rule.*;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public abstract class TacletBuilder<T extends Taclet> {
    protected final static Name NONAME = new Name("unnamed");

    protected Taclet taclet;

    protected Name name = NONAME;
    protected Sequent ifseq = Sequent.EMPTY_SEQUENT;
    protected ImmutableList<NewVarcond> varsNew = ImmutableSLList.nil();
    protected ImmutableList<NotFreeIn> varsNotFreeIn = ImmutableSLList.nil();
    protected ImmutableList<NewDependingOn> varsNewDependingOn =
        ImmutableSLList.nil();
    protected ImmutableList<TacletGoalTemplate> goals = ImmutableSLList.nil();
    protected TacletAttributes attrs = new TacletAttributes(null, null);

    /**
     * List of additional generic conditions on the instantiations of schema variables.
     */
    protected ImmutableList<VariableCondition> variableConditions =
        ImmutableSLList.nil();
    protected ImmutableSet<TacletAnnotation> tacletAnnotations =
        DefaultImmutableSet.nil();

    public void setAnnotations(ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this.tacletAnnotations = tacletAnnotations;
    }

    private static boolean containsFreeVarSV(Term t) {
        // TODO: Fix this
        for (final QuantifiableVariable var : t.freeVars()) {
            if (var instanceof VariableSV) {
                return true;
            }
        }
        return false;
    }

    private static boolean containsFreeVarSV(Sequent sequent) {
        for (final SequentFormula cf : sequent) {
            if (containsFreeVarSV(cf.formula())) {
                return true;
            }
        }
        return false;
    }

    static void checkContainsFreeVarSV(Sequent seq, Name tacletName, String str) {
        if (containsFreeVarSV(seq)) {
            throw new TacletBuilderException(tacletName,
                "Free Variable in " + str + " in Taclet / sequent: " + seq);
        }
    }

    static void checkContainsFreeVarSV(Term t, Name tacletName, String str) {
        if (containsFreeVarSV(t)) {
            throw new TacletBuilderException(tacletName,
                "Free Variable found in " + str + " in Taclet / Term: " + t);
        }
    }

    /**
     * sets the trigger
     */
    public void setTrigger(Trigger trigger) {
        attrs = new TacletAttributes(attrs.displayName(), trigger);
    }

    /**
     * returns the name of the Taclet to be built
     */
    public Name getName() {
        return this.name;
    }

    /**
     * sets the name of the Taclet to be built
     */
    public void setName(Name name) {
        this.name = name;
    }

    /**
     * sets an optional display name (presented to the user)
     */
    public void setDisplayName(String s) {
        attrs = new TacletAttributes(s, attrs.trigger());
    }

    /**
     * sets the ifseq of the Taclet to be built
     */
    public void setIfSequent(Sequent seq) {
        checkContainsFreeVarSV(seq, getName(), "sequent");
        this.ifseq = seq;
    }

    /**
     * adds a new <I>new</I> variable to the variable conditions of the Taclet: v is new and has the
     * same type as peerSV
     */
    public void addVarsNew(SchemaVariable v, SchemaVariable peerSV) {
        addVarsNew(new NewVarcond(v, peerSV));
    }

    /**
     * adds a new <I>new</I> variable to the variable conditions of the Taclet: v is new and has the
     * given type
     */
    public void addVarsNew(SchemaVariable v, KeYRustyType type) {
        if (type == null) {
            throw new NullPointerException("given type is null");
        }
        addVarsNew(new NewVarcond(v, type));
    }

    /**
     * adds a new <I>new</I> variable to the variable conditions of the Taclet: v is new.
     */
    public void addVarsNew(NewVarcond nv) {
        if (!(nv.getSchemaVariable() instanceof ProgramSV)) {
            throw new TacletBuilderException(this, "Tried to add condition:" + nv
                + "to new vars-list. That can" + "match more than program" + " variables.");
        }
        varsNew = varsNew.prepend(nv);
    }

    /**
     * adds a new <I>NotFreeIn</I> variable pair to the variable conditions of the Taclet: v0 is not
     * free in v1.
     */
    public void addVarsNotFreeIn(SchemaVariable v0, SchemaVariable v1) {
        varsNotFreeIn = varsNotFreeIn.prepend(new NotFreeIn(v0, v1));
    }


    public void addVarsNotFreeIn(Iterable<? extends SchemaVariable> v0,
            Iterable<? extends SchemaVariable> v1) {
        for (SchemaVariable boundSV : v0) {
            for (SchemaVariable schemaVar : v1) {
                addVarsNotFreeIn(boundSV, schemaVar);
            }
        }
    }


    public void addVarsNotFreeIn(Iterable<? extends SchemaVariable> v0, SchemaVariable... v1) {
        for (SchemaVariable boundSV : v0) {
            for (SchemaVariable schemaVar : v1) {
                addVarsNotFreeIn(boundSV, schemaVar);
            }
        }
    }

    /**
     * Add a "v0 depending on v1"-statement. "v0" may not occur within the {@code if} sequent or the
     * {@code find}
     * formula/term, however, this is not checked
     */
    public void addVarsNewDependingOn(SchemaVariable v0, SchemaVariable v1) {
        varsNewDependingOn = varsNewDependingOn.prepend(new NewDependingOn(v0, v1));
    }


    /**
     * Add a generic condition on the instantiation of schema variables.
     */
    public void addVariableCondition(VariableCondition vc) {
        variableConditions = variableConditions.append(vc);
    }

    /**
     * adds a new goal descriptions to the goal descriptions of the Taclet. The TacletGoalTemplate
     * must be of the appropriate useKind (Rewrite/Ante/Succ), otherwise an IllegalArgumentException
     * is
     * thrown.
     */
    public abstract void addTacletGoalTemplate(TacletGoalTemplate goal);

    public Sequent ifSequent() {
        return ifseq;
    }

    public ImmutableList<TacletGoalTemplate> goalTemplates() {
        return goals;
    }

    public Iterator<NotFreeIn> varsNotFreeIn() {
        return varsNotFreeIn.iterator();
    }

    /**
     * builds and returns the Taclet that is specified by former set... / add... methods. If no name
     * is specified then a Taclet with an empty string name is build. No specifications for
     * variable conditions, goals or rule sets imply that the corresponding parts of the Taclet are
     * empty. No specification for the if-sequence is represented as a sequent with two empty
     * semisequences. No specification for the interactive or recursive flags imply that the flags
     * are not set. No specified find part for Taclets that require a find part causes an
     * IllegalStateException.
     */
    public abstract T getTaclet();

    public static class TacletBuilderException extends IllegalArgumentException {
        private final Name tacletName;
        private final String errorMessage;

        public TacletBuilderException(Name tacletName, String errorMessage) {
            this.tacletName = tacletName;
            this.errorMessage = errorMessage;
        }

        public TacletBuilderException(TacletBuilder<?> tb, String errorMessage) {
            this(tb.getName(), errorMessage);
        }


        public String getMessage() {
            String message = (tacletName == null ? "(unknown taclet name)" : tacletName.toString());
            return message + ": " + errorMessage;
        }
    }
}
