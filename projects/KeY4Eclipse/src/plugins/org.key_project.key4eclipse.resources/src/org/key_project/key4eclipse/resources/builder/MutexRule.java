package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.runtime.jobs.ISchedulingRule;

public class MutexRule implements ISchedulingRule {
   public boolean isConflicting(ISchedulingRule rule) {
      return rule == this;
   }
   public boolean contains(ISchedulingRule rule) {
      return rule == this;
   }
}
