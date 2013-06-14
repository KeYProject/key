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

package de.hentschel.visualdbc.key.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gmf.runtime.diagram.core.services.ViewService;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.document.DiagramDocument;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.document.IDiagramDocument;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.document.IDocument;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.ui.IEditorInput;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDocumentProvider;

/**
 * Extend the functionality of {@link DbCDocumentProvider} to support {@link DbcModelEditorInput}.
 * @author Martin Hentschel
 */
public class DbCModelDocumentProvider extends DbCDocumentProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ElementInfo createElementInfo(Object element) throws CoreException {
      if (element instanceof DbcModelEditorInput) {
         IEditorInput editorInput = (IEditorInput) element;
         IDiagramDocument document = (IDiagramDocument) createDocument(editorInput);

         ResourceSetInfo info = new ResourceSetInfo(document, editorInput);
         info.setModificationStamp(System.currentTimeMillis());
         info.fStatus = null;
         return info;
      }
      else {
         return super.createElementInfo(element);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IDocument createDocument(Object element) throws CoreException {
      if (element instanceof DbcModelEditorInput) {
         IDocument document = createEmptyDocument();
         setDocumentContent(document, (IEditorInput) element);
         setupDocument(element, document);
         return document;
      }
      else {
         return super.createDocument(element); 
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void setDocumentContent(IDocument document, IEditorInput element) throws CoreException {
      if (element instanceof DbcModelEditorInput) {
         DbcModel model = ((DbcModelEditorInput)element).getModel();
         final TransactionalEditingDomain domain = ((DiagramDocument)document).getEditingDomain();
         final Diagram diagram = ViewService.createDiagram(model, DbcModelEditPart.MODEL_ID, DbCDiagramEditorPlugin.DIAGRAM_PREFERENCES_HINT);
         final Resource resource = domain.createResource("notExisting");
         RecordingCommand cmd = new RecordingCommand(domain) {
            @Override
            protected void doExecute() {
               resource.getContents().add(diagram);
            }
         };
         domain.getCommandStack().execute(cmd);
         document.setContent(diagram);
      }
      else {
         super.setDocumentContent(document, element);
      }
   }
}