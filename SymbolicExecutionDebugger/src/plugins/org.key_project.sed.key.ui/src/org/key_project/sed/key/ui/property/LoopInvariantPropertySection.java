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
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYLoopBodyTermination;
import org.key_project.sed.key.core.model.KeYLoopInvariant;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * {@link ISection} implementation to show the properties of {@link ISENode}s.
 * @author Martin Hentschel
 */
public class LoopInvariantPropertySection extends AbstractTruthValuePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected IKeYSENode<?> getDebugNode() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getDebugNode(object);
   }
   
   /**
    * Converts the given {@link Object} into an {@link IKeYSENode} if possible.
    * @param object The given {@link Object}.
    * @return The {@link IKeYSENode} or {@code null} if conversion is not possible.
    */
   public static IKeYSENode<?> getDebugNode(Object object) {
      return object instanceof KeYLoopInvariant || object instanceof KeYLoopBodyTermination ?
             (IKeYSENode<?>) object :
             null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractTruthValueComposite createContentComposite(Composite parent) {
      return new LoopInvariantComposite(parent, getWidgetFactory(), this);
   }
}