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

package org.key_project.sed.ui.visualization.execution_tree.service;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.impl.IIndependenceSolver;
import org.eclipse.graphiti.ui.features.DefaultFeatureProvider;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.SEPreorderIterator;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Implementation of {@link IIndependenceSolver} which can be used to link
 * {@link ISEDebugElement}s with Graphiti diagram elements. This implementation does
 * the mapping via the the ID of an {@link ISEDebugElement} ({@link ISEDebugElement#getId()}).
 * All other elements are mapped with their hash code value ({@link Object#hashCode()}).
 * </p>
 * <p>
 * To use this {@link IIndependenceSolver} it is required to change the
 * default instance in the constructor of the used {@link DefaultFeatureProvider}
 * via {@code setIndependenceSolver}.
 * </p>
 * @author Martin Hentschel
 */
public class SEIndependenceSolver implements IIndependenceSolver {
   /**
    * Maps the hash code ({@link Object#hashCode()}) to his instance.
    */
   private Map<String, Object> objectHashmap = new HashMap<String, Object>();

   /**
    * <p>
    * Initializes this solver if possible with the given business objects.
    * </p>
    * <p>
    * This method must be executed before {@link #getKeyForBusinessObject(Object)}
    * is called the first time.
    * </p>
    * @param targets The given business objects
    * @throws DebugException Occurred Exception.
    */
   public void init(List<ISEDebugTarget> targets) throws DebugException {
      Assert.isTrue(this.objectHashmap.isEmpty());
      if (targets != null) {
         for (ISEDebugTarget target : targets) {
            ISEIterator iter = new SEPreorderIterator(target);
            while (iter.hasNext()) {
               ISEDebugElement next = iter.next();
               getKeyForBusinessObject(next);
            }
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getKeyForBusinessObject(Object bo) {
      String key;
      if (bo instanceof ISEDebugElement) {
         key = ((ISEDebugElement)bo).getId();
      }
      else {
         key = Integer.toString(ObjectUtil.hashCode(bo));
      }
      objectHashmap.put(key, bo);
      return key;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getBusinessObjectForKey(String key) {
      return key != null ? objectHashmap.get(key) : null;
   }
}