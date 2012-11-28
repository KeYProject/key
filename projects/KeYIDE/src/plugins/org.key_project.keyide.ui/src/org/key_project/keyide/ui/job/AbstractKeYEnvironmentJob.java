package org.key_project.keyide.ui.job;

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ObjectchedulingRule;

import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public abstract class AbstractKeYEnvironmentJob extends Job {
   public AbstractKeYEnvironmentJob(String name, KeYEnvironment<?> environment) {
      super(name);
      setRule(new ObjectchedulingRule(environment));
   }
}
