package org.key_project.sed.key.core.setup;

import org.key_project.util.eclipse.setup.ISetupParticipant;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;

public class StrategyPropertiesSetupParticipant implements ISetupParticipant {
   /**
    * {@inheritDoc}
    */
   @Override
   public void setupWorkspace() {
      StrategyProperties sp = SymbolicExecutionStrategy.getSymbolicExecutionStrategyProperties(true, true, false, false, false, false);
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void startup() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getID() {
      return getClass().getName();
   }
}
