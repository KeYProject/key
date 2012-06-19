package org.key_project.sed.key.core.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;

import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;

/**
 * Initializes the preferences of {@link KeYSEDPreferences} when they are
 * accessed the first time. This is managed by extension point
 * {@code org.eclipse.core.runtime.preferences}.
 * @author Martin Hentschel
 * @see KeYSEDPreferences
 */
public class KeYSEDPreferencesInitializer extends AbstractPreferenceInitializer {
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeDefaultPreferences() {
      KeYSEDPreferences.setDefaultMaximalNumberOfSetNodesPerBranchOnRun(ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN);
   }
}
