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

package org.key_project.keyide.ui.job;

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ObjectsSchedulingRule;

import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * A job that does something with KeY
 * @author Martin Hentschel
 */
public abstract class AbstractKeYEnvironmentJob extends Job {
   /**
    * Constructor
    * @param name The name of this job.
    * @param environment The ProofEnvironment for this job to work in.
    */
   public AbstractKeYEnvironmentJob(String name, KeYEnvironment<?> environment) {
      super(name);
      setRule(new ObjectsSchedulingRule(new Object[] {environment}));
   }
}