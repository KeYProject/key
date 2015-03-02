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

package org.key_project.util.eclipse.job;

import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.java.ArrayUtil;

/**
 * This {@link ISchedulingRule} can be used to let {@link Job}s waiting
 * if they use the same given {@link Object}.
 * @author Martin Hentschel
 */
public class ObjectsSchedulingRule implements ISchedulingRule {
   /**
    * The objects which causes conflicts.
    */
   private final Object[] conflictsWith;
   
   /**
    * Constructor.
    * @param conflictsWith The objects which causes conflicts.
    */
   public ObjectsSchedulingRule(Object[] conflictsWith) {
      this.conflictsWith = conflictsWith;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean contains(ISchedulingRule rule) {
      if (rule instanceof ObjectsSchedulingRule) {
         if (conflictsWith != null) { 
            Object[] otherConflicts = ((ObjectsSchedulingRule)rule).getConflictsWith();
            boolean hasConflictingObject = false;
            int i = 0;
            while (!hasConflictingObject && i < conflictsWith.length) {
               if (ArrayUtil.contains(otherConflicts, conflictsWith[i])) {
                  hasConflictingObject = true;
               }
               i++;
            }
            return hasConflictingObject;
         }
         else {
            return false;
         }
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
    * Returns the objects which causes conflicts.
    * @return The objects which causes conflicts.
    */
   public Object[] getConflictsWith() {
      return conflictsWith;
   }
}