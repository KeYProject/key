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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.emf.workspace.IWorkspaceCommandStack;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.graphiti.ui.internal.editor.DiagramEditorInternal;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

/**
 * A customized {@link DiagramEditorInput} which is not saved in the workbench,
 * resulting in that opened editor with this {@link IEditorInput} are not
 * restored when Eclipse is started the next time.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class NonPersistableDiagramEditorInput extends DiagramEditorInput {
   /**
    * Creates a new {@link NonPersistableDiagramEditorInput} out of a {@link URI} string and
    * a transactional editing domain. For resolving the {@link URI} to an
    * {@link EObject} its {@link ResourceSet} is used. <br>
    * The ResourceSet of the editing domain must have been already set from
    * outside and has to contain an instance of {@link IWorkspaceCommandStack}
    * as the used command stack. <br>
    * A diagram type provider ID is hold in this class.
    * 
    * @param diagramUriString
    *            A {@link URI} string as returned by {@link URI#toString()}
    *            that denotes the input's {@link EObject}
    * @param domain
    *            A {@link TransactionalEditingDomain} which contains the
    *            {@link ResourceSet}. Unless <code>disposeEditingDomain</code>
    *            is set, the caller is responsible for disposing this instance
    *            of the domain when it is no longer needed!
    * @param providerId
    *            A {@link String} which holds the diagram type id. When it is
    *            null, it is set later in {@link DiagramEditorInternal}
    * @param disposeEditingDomain
    *            If set to <code>true</code> this instance of
    *            {@link NonPersistableDiagramEditorInput} will on dispose care about
    *            disposing the passed {@link TransactionalEditingDomain} as
    *            well. If <code>false</code> is passed the caller (or rather
    *            the creator of the domain needs to care about that.
    * @throws IllegalArgumentException
    *             if <code>uriString</code> parameter is null <br>
    *             if the command stack of the passed <code>domain</code> is no
    *             <code>IWorkspaceCommandStack</code>
    * @see URI
    */
   public NonPersistableDiagramEditorInput(String diagramUriString, 
                                           TransactionalEditingDomain domain, 
                                           String providerId, 
                                           boolean disposeEditingDomain) {
      super(diagramUriString, domain, providerId, disposeEditingDomain);
   }

   /**
    * Creates a new {@link NonPersistableDiagramEditorInput} out of a {@link URI} string and
    * a transactional editing domain. For resolving the {@link URI} to an
    * {@link EObject} its {@link ResourceSet} is used. <br>
    * The ResourceSet of the editing domain must have been already set from
    * outside and has to contain an instance of {@link IWorkspaceCommandStack}
    * as the used command stack. <br>
    * A diagram type provider ID is held in this class.
    * 
    * @param diagramUriString
    *            A {@link URI} string as returned by {@link URI#toString()}
    *            that denotes the input's {@link EObject}
    * @param domain
    *            A {@link TransactionalEditingDomain} which contains the
    *            {@link ResourceSet}. Note that the caller is responsible for
    *            disposing this instance of the domain when it is no longer
    *            needed!
    * @param providerId
    *            A {@link String} which holds the diagram type id. When it is
    *            null, it is set later in {@link DiagramEditorInternal}
    * @throws IllegalArgumentException
    *             if <code>uriString</code> parameter is null <br>
    *             if the command stack of the passed <code>domain</code> is no
    *             <code>IWorkspaceCommandStack</code>
    * @see URI
    */
   public NonPersistableDiagramEditorInput(String diagramUriString, 
                                           TransactionalEditingDomain domain, 
                                           String providerId) {
      super(diagramUriString, domain, providerId);
   }

   /**
    * Creates a new {@link NonPersistableDiagramEditorInput} out of a {@link URI} string and
    * a transactional editing domain. For resolving the {@link URI} to an
    * {@link EObject} its {@link ResourceSet} is used. <br>
    * The ResourceSet of the editing domain must have been already set from
    * outside and has to contain an instance of {@link IWorkspaceCommandStack}
    * as the used command stack. <br>
    * A diagram type provider ID is held in this class.
    * 
    * @param diagramUriString
    *            A {@link URI} string as returned by {@link URI#toString()}
    *            that denotes the input's {@link EObject}
    * @param domain
    *            A {@link TransactionalEditingDomain} which contains the
    *            {@link ResourceSet}. Note that the caller is responsible for
    *            disposing this instance of the domain when it is no longer
    *            needed!
    * @param providerId
    *            A {@link String} which holds the diagram type id. When it is
    *            null, it is set later in {@link DiagramEditorInternal}
    * @throws IllegalArgumentException
    *             if <code>uriString</code> parameter is null <br>
    *             if the command stack of the passed <code>domain</code> is no
    *             <code>IWorkspaceCommandStack</code>
    * @see URI
    */
   public NonPersistableDiagramEditorInput(URI diagramUri, 
                                           TransactionalEditingDomain domain, 
                                           String providerId, 
                                           boolean disposeEditingDomain) {
      super(diagramUri, domain, providerId, disposeEditingDomain);
   }

   /**
    * Creates a new {@link NonPersistableDiagramEditorInput} out of a {@link URI} string and
    * a transactional editing domain. For resolving the {@link URI} to an
    * {@link EObject} its {@link ResourceSet} is used. <br>
    * The ResourceSet of the editing domain must have been already set from
    * outside and has to contain an instance of {@link IWorkspaceCommandStack}
    * as the used command stack. <br>
    * A diagram type provider ID is hold in this class.Creates an input out of
    * a {@link URI} string and a transactional editing domain. For resolving
    * the {@link URI} to an {@link EObject} its {@link ResourceSet} is used.
    * The ResourceSet of the editing domain must have been already set from
    * outside. A diagram type provider ID is hold in this class.
    * 
    * @param diagramUri
    *            a {@link URI} that denotes the input's {@link EObject}
    * @param domain
    *            A {@link TransactionalEditingDomain} which contains the
    *            {@link ResourceSet}. Note that the caller is responsible for
    *            disposing this instance of the domain when it is no longer
    *            needed!
    * @param providerId
    *            A {@link String} which holds the diagram type id. When it is
    *            null, it is set later in {@link DiagramEditorInternal}
    * @throws IllegalArgumentException
    *             if <code>uri</code> parameter is null <br>
    *             if the command stack of the passed <code>domain</code> is no
    *             <code>IWorkspaceCommandStack</code>
    * @see #NonPersistableDiagramEditorInput(String, TransactionalEditingDomain)
    * @see URI
    */
   public NonPersistableDiagramEditorInput(URI diagramUri, 
                                           TransactionalEditingDomain domain, 
                                           String providerId) {
      super(diagramUri, domain, providerId);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPersistableElement getPersistable() {
      return null;
   }

   /**
    * Creates a new {@link NonPersistableDiagramEditorInput} with a self created {@link}
    * TransactionalEditingDomain editing domain, which must be disposed later
    * on. <br>
    * The ResourceSet of the editing domain must have been already set from
    * outside and has to contain an instance of {@link IWorkspaceCommandStack}
    * as the used command stack. <br>
    * 
    * @param diagram
    *            A {@link Diagram}
    * @param domain
    *            A {@link TransactionalEditingDomain} which contains the
    *            {@link ResourceSet}
    * @param providerId
    *            A {@link String} which holds the diagram type id.
    * @param disposeEditingDomain
    *            If set to <code>true</code> the created instance of
    *            {@link NonPersistableDiagramEditorInput} will on dispose care about
    *            disposing the passed {@link TransactionalEditingDomain} as
    *            well. If <code>false</code> is passed the caller (or rather
    *            the creator of the domain needs to care about that.
    * @return A {@link NonPersistableDiagramEditorInput} editor input
    */
   public static NonPersistableDiagramEditorInput createEditorInput(Diagram diagram, 
                                                                    TransactionalEditingDomain domain, 
                                                                    String providerId, 
                                                                    boolean disposeEditingDomain) {
      final Resource resource = diagram.eResource();
      if (resource == null) {
         throw new IllegalArgumentException();
      }
      URI diagramUri = EcoreUtil.getURI(diagram);
      NonPersistableDiagramEditorInput diagramEditorInput;
      if (disposeEditingDomain) {
         diagramEditorInput = new NonPersistableDiagramEditorInput(diagramUri, domain, providerId, true);
      } else {
         diagramEditorInput = new NonPersistableDiagramEditorInput(diagramUri, domain, providerId);
      }
      return diagramEditorInput;
   }
}