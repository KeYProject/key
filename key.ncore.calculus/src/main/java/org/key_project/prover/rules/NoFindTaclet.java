package org.key_project.prover.rules;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

/**
 * Used to implement a Taclet that has no <I>find</I> part. This kind of taclet is not attached to
 * term or formula, but to a complete sequent. A typical representant is the <code>cut</code> rule.
 */
public abstract class NoFindTaclet extends Taclet {
    /**
     * creates a {@link Taclet} (previously Schematic Theory Specific Rule) with the given
     * parameters.
     *
     * @param name the name of the Taclet
     * @param applPart contains the application part of a Taclet that is the if-sequent, the
     *        variable conditions
     * @param goalTemplates the IList containing all goal descriptions of the
     *        taclet to be created
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * @param prefixMap a ImmutableMap that contains the prefix for each
     *        SchemaVariable in the Taclet
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public NoFindTaclet(Name name, TacletApplPart applPart,
                        ImmutableList<TacletGoalTemplate> goalTemplates, ImmutableList<RuleSet> ruleSets,
                        TacletAttributes attrs,
                        ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
                        ChoiceExpr choices, ImmutableSet<TacletAnnotation> tacletAnnotations) {
        super(name, applPart, goalTemplates, ruleSets, attrs, prefixMap, choices,
                tacletAnnotations);
    }
}
