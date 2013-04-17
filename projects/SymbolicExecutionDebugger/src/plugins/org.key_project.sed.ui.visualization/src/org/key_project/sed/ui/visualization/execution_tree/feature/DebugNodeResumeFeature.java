/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.commands.IDebugCommandHandler;
import org.eclipse.debug.core.model.ISuspendResume;
import org.eclipse.debug.internal.core.commands.ResumeCommand;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.custom.ICustomFeature;

/**
 * An {@link ICustomFeature} which executes {@link ISuspendResume#resume()}
 * on selected business objects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class DebugNodeResumeFeature extends AbstractDebugNodeSuspendResumeFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public DebugNodeResumeFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canExecute(ISuspendResume suspendResume) {
      return suspendResume.canResume();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IDebugCommandHandler createCommand() {
      return new ResumeCommand();
   }
}