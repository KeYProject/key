/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;


/**
 * An abstract class to represent Taclets with a find part. This means, they have to be attached to
 * a formula or term of the sequent. This class is extended by several subclasses to distinct
 * between taclets that have to attached to a top level formula of the antecedent
 * ({@link AntecTaclet}), to the succedent ({@link SuccTaclet}) or to an arbitrary term that matches
 * the find part somewhere in the sequent ({@link RewriteTaclet}).
 */
public abstract class FindTaclet extends Taclet {

    /** contains the find term */
    protected final Term find;

    /** Set of schemavariables of the if and the (optional) find part */
    private ImmutableSet<SchemaVariable> ifFindVariables = null;

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This is the
     * case if we have an Antec or SuccTaclet but not for a RewriteTaclet
     *
     * @return true if top level updates shall be ignored
     */
    public abstract boolean ignoreTopLevelUpdates();


    /**
     * creates a FindTaclet
     *
     * @param name the Name of the taclet
     * @param applPart the TacletApplPart that contains the if-sequent, the not-free and new-vars
     *        conditions
     * @param goalTemplates a IList<TacletGoalTemplate> that contains all goaltemplates of the
     *        taclet (these are the instructions used to create new goals when applying the Taclet)
     * @param ruleSets a IList<RuleSet> that contains all rule sets the Taclet is attached to
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive, recursive or
     *        something like that
     * @param find the Term that is the pattern that has to be found in a sequent and the places
     *        where it matches the Taclet can be applied
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    protected FindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, Term find, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices, boolean surviveSymbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, prefixMap, choices, surviveSymbExec,
            tacletAnnotations);
        this.find = find;
    }

    /**
     * creates a FindTaclet
     *
     * @param name the Name of the taclet
     * @param applPart the TacletApplPart that contains the if-sequent, the not-free and new-vars
     *        conditions
     * @param goalTemplates a IList<TacletGoalTemplate> that contains all goaltemplates of the
     *        taclet (these are the instructions used to create new goals when applying the Taclet)
     * @param ruleSets a IList<RuleSet> that contains all rule sets the Taclet is attached to
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive, recursive or
     *        something like that
     * @param find the Term that is the pattern that has to be found in a sequent and the places
     *        where it matches the Taclet can be applied
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    protected FindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> ruleSets,
            TacletAttributes attrs, Term find, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ChoiceExpr choices, ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, choices, false,
            tacletAnnotations);
    }

    /** returns the find term of the taclet to be matched */
    public Term find() {
        return find;
    }


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
            sb = sb.append(name()).append(" {\n");
            sb = toStringIf(sb);
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


    /**
     * @return Set of schemavariables of the if and the (optional) find part
     */
    public ImmutableSet<SchemaVariable> getIfFindVariables() {
        if (ifFindVariables == null) {
            TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector();
            find().execPostOrder(svc);

            ifFindVariables = getIfVariables();

            for (final SchemaVariable sv : svc.vars()) {
                ifFindVariables = ifFindVariables.add(sv);
            }
        }

        return ifFindVariables;
    }

    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }
        return find.equals(((FindTaclet) o).find);
    }


    public int hashCode() {
        return 13 * super.hashCode() + find.hashCode();
    }

    /**
     * returns the variables that occur bound in the find part
     */
    protected ImmutableSet<QuantifiableVariable> getBoundVariablesHelper() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(find());
        return bvv.getBoundVariables();
    }

}
