package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;

public class ContainsLabelFeature extends BinaryFeature {

    private final TermLabel label;


    public ContainsLabelFeature(TermLabel label) {
        this.label = label;
    }



    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        return pos != null && pos.subTerm().containsLabel(label);
    }

}
