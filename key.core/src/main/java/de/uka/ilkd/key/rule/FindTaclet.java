/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.*;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.TacletAnnotation;
import org.key_project.prover.rules.TacletApplPart;
import org.key_project.prover.rules.TacletAttributes;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;


/**
 * An abstract class to represent Taclets with a find part. This means, they have to be attached to
 * a formula or term of the sequent. This class is extended by several subclasses to distinct
 * between taclets that have to attached to a top level formula of the antecedent
 * ({@link AntecTaclet}), to the succedent ({@link SuccTaclet}) or to an arbitrary term that matches
 * the find part somewhere in the sequent ({@link RewriteTaclet}).
 */
public abstract class FindTaclet extends Taclet {
    /** Set of schema variables of the assumes sequent and the (optional) find expression/sequent */
    private ImmutableSet<SchemaVariable> assumesAndFindSchemaVariables = null;

    /**
     * creates a FindTaclet
     *
     * @param name the Name of the taclet
     * @param applPart the TacletApplPart that contains the if-sequent, the not-free and new-vars
     *        conditions
     * @param goalTemplates a IList<TacletGoalTemplate> that contains all goaltemplates of the
     *        taclet (these are the instructions used to create new goals when applying the Taclet)
     * @param ruleSets a ImmutableList that contains all rule sets the Taclet is attached to
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive, recursive or
     *        something like that
     * @param find the Term that is the pattern that has to be found in a sequent and the places
     *        where it matches the Taclet can be applied
     * @param prefixMap a ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    protected FindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, SyntaxElement find,
            ImmutableMap<@NonNull SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            ChoiceExpr choices, boolean surviveSymbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, find, applPart, goalTemplates, ruleSets, attrs, prefixMap, choices,
            surviveSymbExec,
            tacletAnnotations);
    }

    /**
     * creates a FindTaclet
     *
     * @param name the Name of the taclet
     * @param applPart the TacletApplPart that contains the if-sequent, the not-free and new-vars
     *        conditions
     * @param goalTemplates an ImmutableList that contains all goaltemplates of the
     *        taclet (these are the instructions used to create new goals when applying the Taclet)
     * @param ruleSets an ImmutableList that contains all rule sets the Taclet is attached to
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive, recursive or
     *        something like that
     * @param find the Term that is the pattern that has to be found in a sequent and the places
     *        where it matches the Taclet can be applied
     * @param prefixMap an ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    protected FindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, SyntaxElement find,
            ImmutableMap<@NonNull SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
            ChoiceExpr choices, ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, choices, false,
            tacletAnnotations);
    }

    /**
     * returns the find term of the taclet to be matched
     */
    public abstract JTerm find();

    /**
     * @return Set of schemavariables of the if and the (optional) find part
     */
    public ImmutableSet<SchemaVariable> getAssumesAndFindVariables() {
        if (assumesAndFindSchemaVariables == null) {
            TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector();
            find().execPostOrder(svc);

            assumesAndFindSchemaVariables = getAssumesVariables();

            for (final SchemaVariable sv : svc.vars()) {
                assumesAndFindSchemaVariables = assumesAndFindSchemaVariables.add(sv);
            }
        }

        return assumesAndFindSchemaVariables;
    }

    /**
     * returns the variables that occur bound in the find part
     */
    protected ImmutableSet<QuantifiableVariable> getBoundVariablesHelper() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(find());
        return bvv.getBoundVariables();
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }
        return find.equals(((FindTaclet) o).find);
    }

    /** {@inheritDoc} */
    public int hashCode() {
        return 13 * super.hashCode() + find.hashCode();
    }

    /**
     * appends a string representation of the find expression to the provided stringbuffer
     *
     * @param sb the StringBuffer where to append the find expression
     * @return the same StringBuffer as the one given as argument
     */
    protected StringBuffer toStringFind(StringBuffer sb) {
        return sb.append("\\find(").append(find().toString()).append(")\n");
    }

    /**
     * returns a representation of the Taclet with find part as String
     *
     * @return string representation
     */
    public String toString() {
        if (tacletAsString == null) {
            StringBuffer sb = new StringBuffer();
            sb.append(name()).append(" {\n");
            sb = toStringAssumes(sb);
            sb = toStringFind(sb);
            sb = toStringVarCond(sb);
            sb = toStringGoalTemplates(sb);
            sb = toStringRuleSets(sb);
            sb = toStringAttribs(sb);
            sb = toStringTriggers(sb);
            tacletAsString = sb.append("}").toString();
        }
        return tacletAsString;
    }
}
