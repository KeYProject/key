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

package org.key_project.sed.ui.visualization.object_diagram.editor;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.ide.IDE;
import org.key_project.sed.ui.visualization.object_diagram.perspective.StateVisualizationPerspectiveFactory;
import org.key_project.sed.ui.visualization.object_diagram.provider.ObjectDiagramTypeProvider;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.NonPersistableDiagramEditorInput;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.StringUtil;

/**
 * Read-only {@link ObjectDiagramEditor}.
 * @author Martin Hentschel
 */
public class ReadonlyObjectDiagramEditor extends ObjectDiagramEditor {
   /**
    * The ID of this editor.
    */
   public static final String EDITOR_ID = "org.key_project.sed.ui.visualization.ReadonlyObjectDiagramEditor";

   /**
    * Constructor.
    */
   public ReadonlyObjectDiagramEditor() {
      setPaletteHidden(true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void configureGraphicalViewer() {
      super.configureGraphicalViewer();
      setGridVisible(false);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return false;
   }
   
   /**
    * Opens a {@link ReadonlyObjectDiagramEditor}.
    * @param page The {@link IWorkbenchPage} to open editor in..
    * @param diagramName The name of the diagram.
    * @param uniqueId A unique ID to identify the opened file.
    * @return The opened {@link ReadonlyObjectDiagramEditor} or the returned one if a file with the given ID is already opened.
    * @throws PartInitException Occurred Exception.
    */
   public static ReadonlyObjectDiagramEditor openEditor(IWorkbenchPage page, String diagramName, String uniqueId) throws PartInitException {
      // Create empty diagram
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ObjectDiagramTypeProvider.TYPE, 
                                                                    StringUtil.toSingleLinedString(diagramName), 
                                                                    true);
      // Create editing domain and resource that contains the diagram
      URI uri = URI.createURI(uniqueId + ObjectDiagramUtil.DIAGRAM_AND_MODEL_FILE_EXTENSION_WITH_DOT);
      TransactionalEditingDomain domain = GraphitiUtil.createDomainAndResource(diagram, uri);
      IEditorInput input = NonPersistableDiagramEditorInput.createEditorInput(diagram, domain, ObjectDiagramTypeProvider.PROVIDER_ID, true);
      // Open editor
      IEditorPart editorPart = IDE.openEditor(page, 
                                              input, 
                                              ReadonlyObjectDiagramEditor.EDITOR_ID);
      if (ObjectDiagramUtil.shouldSwitchToStateVisualizationPerspective(page)) {
         WorkbenchUtil.openPerspective(StateVisualizationPerspectiveFactory.PERSPECTIVE_ID);
      }
      Assert.isTrue(editorPart instanceof ReadonlyObjectDiagramEditor);
      return (ReadonlyObjectDiagramEditor)editorPart;
   }
}