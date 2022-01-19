package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import org.key_project.util.collection.ImmutableList;

/**
 * The rule application for {@link JmlAssertRule}
 *
 * @author Benjamin Takacs
 */
public class JmlAssertBuiltInRuleApp extends AbstractBuiltInRuleApp {

    /**
     * @param rule the rule being applied
     * @param occurrence the position at which the rule is applied
     */
    public JmlAssertBuiltInRuleApp(BuiltInRule rule, PosInOccurrence occurrence) {
        super(rule, occurrence);
        assert rule instanceof JmlAssertRule;
        assert occurrence != null;
    }

    @Override
    public JmlAssertBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new JmlAssertBuiltInRuleApp(rule(), newPos);
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        //XXX: no idea what I'm doing here, just copied code from elsewhere
        //     what should this methode even do, there is no javadoc

        // seems like all subclasses of  AbstractBuiltInRuleApp  do it like that
        // maybe move it there?
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }
}
