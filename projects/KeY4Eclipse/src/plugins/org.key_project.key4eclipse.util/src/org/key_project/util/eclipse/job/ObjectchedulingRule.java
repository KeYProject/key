package org.key_project.util.eclipse.job;

import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.Job;

/**
 * This {@link ISchedulingRule} can be used to let {@link Job}s waiting
 * if they use the same given {@link Object}.
 * @author Martin Hentschel
 */
public class ObjectchedulingRule implements ISchedulingRule {
   /**
    * The object which causes conflicts.
    */
   private Object conflictsWith;
   
   /**
    * Constructor.
    * @param conflictsWith The object which causes conflicts.
    */
   public ObjectchedulingRule(Object conflictsWith) {
      super();
      this.conflictsWith = conflictsWith;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean contains(ISchedulingRule rule) {
      if (conflictsWith != null && rule instanceof ObjectchedulingRule) {
         ObjectchedulingRule otherRule = (ObjectchedulingRule)rule;
         return conflictsWith.equals(otherRule.getConflictsWith());
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isConflicting(ISchedulingRule rule) {
      return contains(rule);
   }

   /**
    * Returns the object which causes conflicts.
    * @return The object which causes conflicts.
    */
   public Object getConflictsWith() {
      return conflictsWith;
   }
}
