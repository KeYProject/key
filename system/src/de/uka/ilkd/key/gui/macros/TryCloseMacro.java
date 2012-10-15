package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.InteractiveProver;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * The Class TryCloseMacro tries to close goals. Goals are either closed or left
 * untouched.
 * 
 * This uses the code provided by Michael in {@link InteractiveProver}
 * .AutoWorker
 * 
 * @author mattias ulbrich
 */
public class TryCloseMacro implements ProofMacro {

    @Override 
    public String getName() {
        return "Close provable goals";
    }

    @Override 
    public String getDescription() {
        return "Closes closable goals, leave rest untouched (see settings AutoPrune)";
    }

    @Override 
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return true;
    }

    @Override 
    public void applyTo(final KeYMediator mediator, PosInOccurrence posInOcc) {

        final Proof proof = mediator.getInteractiveProver().getProof();
        final StrategySettings strategySettings = proof.getSettings().getStrategySettings();

        // this returns a clone of the actual settings, ...
        final StrategyProperties properties = 
                strategySettings.getActiveStrategyProperties();

        final String oldRetreatMode = 
                properties.getProperty(StrategyProperties.RETREAT_MODE_OPTIONS_KEY);

        properties.put(StrategyProperties.RETREAT_MODE_OPTIONS_KEY, 
                StrategyProperties.RETREAT_MODE_RETREAT);

        // ... we only had a clone, so we need to replace the original settings.
        strategySettings.setActiveStrategyProperties(properties);

        mediator.startAutoMode();

        mediator.addAutoModeListener(new AutoModeListener() {

            @Override 
            public void autoModeStopped(ProofEvent e) {
                properties.put(StrategyProperties.RETREAT_MODE_OPTIONS_KEY, oldRetreatMode);
                strategySettings.setActiveStrategyProperties(properties);
                mediator.removeAutoModeListener(this);
            }

            @Override 
            public void autoModeStarted(ProofEvent e) {
            }
        });

    }

}
