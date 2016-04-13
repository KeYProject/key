/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.util;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.swt.graphics.RGB;

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
      KeYSEDPreferences.setDefaultShowMethodReturnValuesInDebugNode(true);
      KeYSEDPreferences.setDefaultShowVariablesOfSelectedDebugNode(true);
      KeYSEDPreferences.setDefaultShowKeYMainWindow(false);
      KeYSEDPreferences.setDefaultMergeBranchConditions(false);
      KeYSEDPreferences.setDefaultUseUnicode(false);
      KeYSEDPreferences.setDefaultUsePrettyPrinting(true);
      KeYSEDPreferences.setDefaultShowSignatureOnMethodReturnNodes(false);
      KeYSEDPreferences.setDefaultVariablesAreOnlyComputedFromUpdates(false);
      KeYSEDPreferences.setDefaultTruthValueTracingEnabled(false);
      KeYSEDPreferences.setDefaultHighlightReachedSourceCode(true);
      KeYSEDPreferences.setDefaultGroupingEnabled(true);
      KeYSEDPreferences.setDefaultSimplifyConditions(true);
      KeYSEDPreferences.setDefaultTruthValueTracingTrue(new RGB(0, 117, 0));
      KeYSEDPreferences.setDefaultTruthValueTracingFalse(new RGB(170, 0, 0));
      KeYSEDPreferences.setDefaultTruthValueTracingUnknown(new RGB(217, 108, 0));
      KeYSEDPreferences.setDefaultHideFullBranchConditionIfAdditionalLabelIsAvailable(false);
   }
}