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

package org.key_project.sed.key.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.core.model.ISEJoin;
import org.key_project.sed.key.core.model.KeYJoin;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISEJoin}s.
 * @author Martin Hentschel
 */
public class WeakeningPropertySection extends AbstractTruthValuePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected KeYJoin getDebugNode() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugNode(object);
   }
   
   /**
    * Converts the given {@link Object} into a {@link KeYJoin} if possible.
    * @param object The given {@link Object}.
    * @return The {@link KeYJoin} or {@code null} if conversion is not possible.
    */
   public static KeYJoin getDebugNode(Object object) {
      if (object instanceof KeYJoin) {
         KeYJoin join = (KeYJoin) object;
         if (join.isWeakeningVerificationSupported()) {
            return join;
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractTruthValueComposite createContentComposite(Composite parent) {
      return new WeakeningComposite(parent, getWidgetFactory(), this);
   }
}