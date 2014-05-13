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

package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.context.IPictogramElementContext;
import org.eclipse.graphiti.tb.DefaultToolBehaviorProvider;
import org.eclipse.graphiti.tb.IContextButtonPadData;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * {@link IToolBehaviorProvider} specific implementation for object diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramToolBehaviorProvider extends DefaultToolBehaviorProvider {
   /**
    * Indicates that the diagram is read-only or editable.
    */
   private boolean readOnly = false;
   
   /**
    * Constructor.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} in which this {@link IToolBehaviorProvider} is used.
    */
   public ObjectDiagramToolBehaviorProvider(IDiagramTypeProvider diagramTypeProvider) {
      super(diagramTypeProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IContextButtonPadData getContextButtonPad(IPictogramElementContext context) {
      IContextButtonPadData data = super.getContextButtonPad(context);
      if (isReadOnly()) {
         data.getGenericContextButtons().clear();
      }
      return data;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equalsBusinessObjects(Object o1, Object o2) {
      return ObjectUtil.equals(o1, o2); // Used equals method instead of the default equality which returns true if both object contains the same values.
   }

   /**
    * Checks if the diagram is read-only or editable.
    * @return {@code true} read-only, {@code false} editable.
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * Defines if the diagram is read-only or editable.
    * @param readOnly {@code true} read-only, {@code false} editable.
    */
   public void setReadOnly(boolean readOnly) {
      this.readOnly = readOnly;
   }
}