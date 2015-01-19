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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.key.core.model.IKeYTerminationNode;
import org.key_project.sed.key.core.model.KeYMethodContract;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public class PreconditionPropertySection extends AbstractPredicatePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected KeYMethodContract getDebugNode() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugNode(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link IKeYTerminationNode} if possible.
    * @param object The given {@link Object}.
    * @return The {@link IKeYTerminationNode} or {@code null} if conversion is not possible.
    */
   public static KeYMethodContract getDebugNode(Object object) {
      return object instanceof KeYMethodContract ? (KeYMethodContract)object : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractPredicateComposite createContentComposite(Composite parent) {
      return new PreconditionComposite(parent, getWidgetFactory());
   }
}