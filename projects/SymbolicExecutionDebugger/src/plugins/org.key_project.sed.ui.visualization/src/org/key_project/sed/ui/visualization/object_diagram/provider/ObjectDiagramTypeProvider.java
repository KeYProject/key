/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import org.eclipse.graphiti.dt.AbstractDiagramTypeProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.key_project.sed.ui.visualization.object_diagram.editor.ReadonlyObjectDiagramEditor;

/**
 * {@link IDiagramTypeProvider} specific implementation for object diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramTypeProvider extends AbstractDiagramTypeProvider {
   /**
    * The type name which is the unique identifier in diagrams.
    */
   public static final String TYPE = "objectDiagram";

   /**
    * The provider ID of this {@link IDiagramTypeProvider}.
    */
   public static final String PROVIDER_ID = "org.key_project.sed.ui.graphiti.ObjectDiagramTypeProvider";

   /**
    * Contains the available {@link IToolBehaviorProvider}s which are instantiated
    * lazily via {@link #getAvailableToolBehaviorProviders()}.
    */
   private ObjectDiagramToolBehaviorProvider[] toolBehaviorProviders;
   
   /**
    * Constructor.
    */
   public ObjectDiagramTypeProvider() {
      super();
      setFeatureProvider(new ObjectDiagramFeatureProvider(this));
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(Diagram diagram, IDiagramEditor diagramEditor) {
      // Make sure that the editor is compatible with this diagram
      if (diagramEditor instanceof ReadonlyObjectDiagramEditor) {
         getFeatureProvider().setReadOnly(true);
         for (ObjectDiagramToolBehaviorProvider behaviorProvider : getAvailableToolBehaviorProviders()) {
            behaviorProvider.setReadOnly(true);
         }
      }
      // Initialize type provider
      super.init(diagram, diagramEditor);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ObjectDiagramToolBehaviorProvider[] getAvailableToolBehaviorProviders() {
      if (toolBehaviorProviders == null) {
         toolBehaviorProviders = new ObjectDiagramToolBehaviorProvider[] {new ObjectDiagramToolBehaviorProvider(this)};
      }
      return toolBehaviorProviders;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ObjectDiagramFeatureProvider getFeatureProvider() {
      return (ObjectDiagramFeatureProvider)super.getFeatureProvider();
   }
}