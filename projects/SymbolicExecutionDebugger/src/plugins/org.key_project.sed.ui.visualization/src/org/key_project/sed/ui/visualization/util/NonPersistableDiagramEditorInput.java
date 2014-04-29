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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

/**
 * A customized {@link DiagramEditorInput} which is not saved in the workbench,
 * resulting in that opened editor with this {@link IEditorInput} are not
 * restored when Eclipse is started the next time.
 * @author Martin Hentschel
 */
public class NonPersistableDiagramEditorInput extends DiagramEditorInput {
   /**
    * Creates a new {@link NonPersistableDiagramEditorInput} out of a {@link URI} string and
    * a Graphiti diagram type provider ID. For resolving the {@link URI} to an
    * {@link EObject} the {@link ResourceSet} that will be created when a
    * diagram editor starts is taken. This input object will not resolve the
    * diagram.<br>
    * A diagram type provider ID is held in this class.
    * @param diagramUri 
    *            A {@link URI} that denotes the input's {@link EObject}. This
    *            can either be a URI of a Graphiti diagram or the URI of an EMF
    *            resource storing a Graphiti diagram. In the latter case the
    *            given URI will b e trimmed to point to the first element in
    *            the resource; make sure that this lemenet is a Graphiti
    *            diagram, otherwise an exception will be thrown when the
    *            diagram editor opens. No check on this is done inside the
    *            input object itself!
    * @param providerId 
    *            A {@link String} which holds the diagram type id. When it is
    *            null, it is set later in
    *            {@link DiagramEditor#setInput(IEditorInput)}
    */
   public NonPersistableDiagramEditorInput(URI diagramUri, String providerId) {
      super(diagramUri, providerId);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPersistableElement getPersistable() {
      return null;
   }
}