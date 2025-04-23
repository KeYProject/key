package org.key_project.prover.rules;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

public abstract class FindTaclet extends Taclet{
    /** contains the find term */
    protected final Term find;

    /** Set of schema variables of the assumes sequent and the (optional) find expression/sequent */
    protected ImmutableSet<SchemaVariable> assumesAndFindSchemaVariables = null;

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This is the
     * case if we have an AntecTaclet or SuccTaclet but not for a RewriteTaclet
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
                         TacletAttributes attrs, Term find,
                         ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
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
                         TacletAttributes attrs, Term find,
                         ImmutableMap<@NonNull SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap,
                         ChoiceExpr choices, ImmutableSet<TacletAnnotation> tacletAnnotations) {
        this(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, choices, false,
                tacletAnnotations);
    }

    /** returns the find term of the taclet to be matched */
    public Term find() {
        return find;
    }

    /**
     * @return Set of schemavariables of the if and the (optional) find part
     */
    public abstract ImmutableSet<SchemaVariable> getAssumesAndFindVariables();

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
