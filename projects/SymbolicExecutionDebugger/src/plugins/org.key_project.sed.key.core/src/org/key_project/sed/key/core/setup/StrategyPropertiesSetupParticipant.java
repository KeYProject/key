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
      StrategyProperties sp = SymbolicExecutionStrategy.DEFAULT_FACTORY.createDefaultStrategyProperties();
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