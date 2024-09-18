/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.logic.BoundVarsVisitor;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.tacletbuilder.TacletGoalTemplate;
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

    /** Set of schemavariables of the {@code if} and the (optional) {@code find} part */
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
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive, recursive or
     *        something like that
     * @param find the Term that is the pattern that has to be found in a sequent and the places
     *        where it matches the Taclet can be applied
     * @param prefixMap a ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    protected FindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            TacletAttributes attrs, Term find, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            boolean surviveSymbExec,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, attrs, prefixMap, surviveSymbExec,
            tacletAnnotations);
        this.find = find;
    }

    /**
     * creates a FindTaclet
     *
     * @param name the Name of the taclet
     * @param applPart the TacletApplPart that contains the if-sequent, the not-free and new-vars
     *        conditions
     * @param goalTemplates an ImmutableList that contains all goaltemplates of the
     *        taclet (these are the instructions used to create new goals when applying the Taclet)
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive, recursive or
     *        something like that
     * @param find the Term that is the pattern that has to be found in a sequent and the places
     *        where it matches the Taclet can be applied
     * @param prefixMap an ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    protected FindTaclet(Name name, TacletApplPart applPart,
            ImmutableList<TacletGoalTemplate> goalTemplates,
            TacletAttributes attrs, Term find, ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
            ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, attrs, find, prefixMap, false,
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
            sb = toStringAssumes(sb);
            sb = toStringFind(sb);
            sb = toStringVarCond(sb);
            sb = toStringGoalTemplates(sb);
            sb = toStringTriggers(sb);
            tacletAsString = sb.append("}").toString();
        }
        return tacletAsString;
    }


    /**
     * @return Set of schemavariables of the {@code if} and the (optional) {@code find} part
     */
    public ImmutableSet<SchemaVariable> getAssumesAndFindVariables() {
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
