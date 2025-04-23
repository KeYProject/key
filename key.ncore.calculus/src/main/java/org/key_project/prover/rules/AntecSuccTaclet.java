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

/**
 * An AntecSuccTaclet represents a taclet whose find part has to match a top level formula in the
 * antecedent or succedent of the sequent.
 */
public abstract class AntecSuccTaclet extends FindTaclet {
    private final boolean ignoreTopLevelUpdates;

    private final boolean isAntec;

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given parameters.
     *
     * @param name the name of the Taclet
     * @param isAntec whether this taclet matches the antecedent or succedent.
     * @param applPart contains the application part of a Taclet that is the assumes-sequent, the
     *        variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param heuristics a list of heuristics for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values indicating a non-interactive
     *        or recursive use of the Taclet.
     * @param find the find term of the Taclet
     * @param prefixMap a ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     */
    public AntecSuccTaclet(Name name, boolean isAntec, TacletApplPart applPart,
                       ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> heuristics,
                       TacletAttributes attrs, Term find, boolean ignoreTopLevelUpdates,
                       ImmutableMap<@NonNull SchemaVariable, TacletPrefix> prefixMap,
                       ChoiceExpr choices,
                       ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, heuristics, attrs, find, prefixMap, choices,
                tacletAnnotations);
        this.isAntec = isAntec;
        this.ignoreTopLevelUpdates = ignoreTopLevelUpdates;
        createTacletServices();
    }

    /**
     * this method is used to determine if top level updates are allowed to be ignored. This may be
     * the case if we have an Antec or SuccTaclet but not for a RewriteTaclet
     *
     * @return true if top level updates shall be ignored
     */
    @Override
    public boolean ignoreTopLevelUpdates() {
        return ignoreTopLevelUpdates;
    }

    public boolean isAntec() {
        return isAntec;
    }

    /** toString for the find part */
    @Override
    protected StringBuffer toStringFind(StringBuffer sb) {
        if (isAntec)
            return sb.append("\\find(").append(find().toString()).append("==>)\n");
        return sb.append("\\find(==>").append(find().toString()).append(")\n");
    }
}
