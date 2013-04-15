package org.key_project.keyide.ui.job;

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ObjectchedulingRule;

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
      setRule(new ObjectchedulingRule(environment));
   }
}