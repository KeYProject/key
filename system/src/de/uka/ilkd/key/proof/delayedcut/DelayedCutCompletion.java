package de.uka.ilkd.key.proof.delayedcut;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

public interface DelayedCutCompletion {
    public boolean complete(TacletApp app, Goal goal);
}
