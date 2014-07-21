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

package org.key_project.key4eclipse.common.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.key4eclipse.common.ui.starter.IProofStarter;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;

/**
 * A {@link PropertyTester} which checks if the proof start functionality
 * via {@link IProofStarter}s is available or not.
 * @author Martin Hentschel
 */
public class ProofStarterAvailablePropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      return StarterUtil.areProofStartersAvailable();
   }
}