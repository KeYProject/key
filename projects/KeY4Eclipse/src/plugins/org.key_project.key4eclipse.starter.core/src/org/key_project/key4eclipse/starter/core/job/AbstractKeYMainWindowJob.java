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

package org.key_project.key4eclipse.starter.core.job;

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ObjectchedulingRule;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * <p>
 * Provides a basic implementation of {@link Job}s which does something
 * with the {@link MainWindow} of KeY.
 * </p>
 * <p>
 * It is not possible to execute multiple {@link AbstractKeYMainWindowJob}
 * instances at the same time. It is ensured thanks to an
 * {@link ObjectchedulingRule} that uses the class of {@link MainWindow}
 * as conflicting {@link Object}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractKeYMainWindowJob extends Job {
   /**
    * Constructor.
    * @param name The name of this {@link Job}.
    */
   public AbstractKeYMainWindowJob(String name) {
      super(name);
      setRule(new ObjectchedulingRule(MainWindow.class));
   }
}