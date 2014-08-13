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

package org.key_project.sed.key.ui.launch;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jdt.debug.ui.breakpoints.JavaBreakpointConditionEditor;
import org.eclipse.jdt.internal.debug.ui.JDIDebugUIPlugin;
import org.eclipse.jdt.internal.debug.ui.JDISourceViewer;
import org.eclipse.jdt.internal.debug.ui.contentassist.IJavaDebugContentAssistContext;
import org.eclipse.jdt.internal.debug.ui.contentassist.JavaDebugContentAssistProcessor;
import org.eclipse.jdt.internal.debug.ui.display.DisplayViewerConfiguration;
import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.fieldassist.ControlDecoration;
import org.eclipse.jface.fieldassist.FieldDecoration;
import org.eclipse.jface.fieldassist.FieldDecorationRegistry;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.FocusAdapter;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.graphics.FontMetrics;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchCommandConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.IHandlerActivation;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.services.IDisposable;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.key_project.util.bean.Bean;
import org.key_project.util.bean.IBean;

/**
 * <p>
 * This {@link IBean} contains an {@link JDISourceViewer} which
 * can be used to show a Java source snippet.
 * </p>
 * <p>
 * The design of this class is oriented on {@link JavaBreakpointConditionEditor}.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class JavaSnippetSourceViewer extends Bean implements IDisposable {
   /**
    * Property of {@link #getText()}.
    */
   public static final String PROP_TEXT = "text";
   
   /**
    * The shown and used {@link JDISourceViewer}.
    */
   private JDISourceViewer fViewer;

   /**
    * {@link IHandler} for code completion.
    */
   private IHandler fContentAssistHandler;
   
   /**
    * {@link IHandlerActivation} of {@link #fContentAssistHandler}.
    */
   private IHandlerActivation fContentAssistActivation;

   /**
    * {@link IHandler} for undo.
    */
   private IHandler fUndoHandler;
   
   /**
    * {@link IHandlerActivation} of {@link #fUndoHandler}.
    */
   private IHandlerActivation fUndoActivation;
   
   /**
    * {@link IHandler} for redo.
    */
   private IHandler fRedoHandler;
   
   /**
    * {@link IHandlerActivation} of {@link #fRedoHandler}.
    */
   private IHandlerActivation fRedoActivation;
   
   /**
    * The {@link IHandlerService} of the {@link IWorkbench}.
    */
   private IHandlerService fHandlerService;

   /**
    * The last known text of {@link #fViewer}.
    */
   private String oldText;
   
   /**
    * The used {@link ControlDecoration}.
    */
   private ControlDecoration decoration;
   
   /**
    * Observes changes on the document of {@link #fViewer}.
    */
   private IDocumentListener fDocumentListener = new IDocumentListener() {
      @Override
      public void documentChanged(DocumentEvent event) {
         String newText = getText();
         firePropertyChange(PROP_TEXT, oldText, newText);
         oldText = newText;
      }
      
      @Override
      public void documentAboutToBeChanged(DocumentEvent event) {
      }
   };
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    */
   public JavaSnippetSourceViewer(Composite parent) {
      this(parent, SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL | SWT.LEFT_TO_RIGHT);
   }

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    */
   public JavaSnippetSourceViewer(Composite parent, int style) {
      fViewer = new JDISourceViewer(parent, null, style);
      decorateViewer();
      
      GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true);
      // set height/width hints based on font
      GC gc = new GC(fViewer.getTextWidget());
      gc.setFont(fViewer.getTextWidget().getFont());
      FontMetrics fontMetrics = gc.getFontMetrics();
      //gd.heightHint = Dialog.convertHeightInCharsToPixels(fontMetrics, 10);
      gd.widthHint = Dialog.convertWidthInCharsToPixels(fontMetrics, 40);
      gc.dispose();
      getControl().setLayoutData(gd);
      
      fContentAssistHandler = new AbstractHandler() {
         public Object execute(ExecutionEvent event) throws org.eclipse.core.commands.ExecutionException {
            fViewer.doOperation(ISourceViewer.CONTENTASSIST_PROPOSALS);
            return null;
         }
      };
      fUndoHandler = new AbstractHandler() {
         public Object execute(ExecutionEvent event) throws org.eclipse.core.commands.ExecutionException {
            fViewer.doOperation(ITextOperationTarget.UNDO);
            return null;
         }
      };
      fRedoHandler = new AbstractHandler() {
         public Object execute(ExecutionEvent event) throws org.eclipse.core.commands.ExecutionException {
            fViewer.doOperation(ITextOperationTarget.REDO);
            return null;
         }
      };
      
      fHandlerService = (IHandlerService)PlatformUI.getWorkbench().getAdapter(IHandlerService.class);
      getControl().addFocusListener(new FocusAdapter() {
         public void focusGained(FocusEvent e) {
            activateHandlers();
         }
         public void focusLost(FocusEvent e) {
            deactivateHandlers();
         }           
      });
      
      // Set new document
      IDocument document = new Document();
      document.addDocumentListener(fDocumentListener);
      JDIDebugUIPlugin.getDefault().getJavaTextTools().setupJavaDocumentPartitioner(document, IJavaPartitions.JAVA_PARTITIONING);
      fViewer.setInput(document);
   }
   
   /**
    * Adds or removes the decoration of the viewer based on {@link #isEditable()}.
    */
   protected void decorateViewer() {
      if (isEditable()) {
         decoration = new ControlDecoration(getControl(), SWT.TOP | SWT.LEFT);
         decoration.setShowOnlyOnFocus(true);
         FieldDecoration dec = FieldDecorationRegistry.getDefault().getFieldDecoration(FieldDecorationRegistry.DEC_CONTENT_PROPOSAL);
         decoration.setImage(dec.getImage());
         decoration.setDescriptionText(dec.getDescription());
      }
      else {
         if (decoration != null) {
            decoration.dispose();
            decoration = null;
         }
      }
   }
   
   /**
    * Returns the shown decoration {@link Image} if available.
    * @return The decoration {@link Image} or {@code null} if no one is used.
    */
   public Image getDecoractionImage() {
      return decoration != null ? decoration.getImage() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      deactivateHandlers();
      fViewer.dispose();
      if (decoration != null) {
         decoration.dispose();
      }
   }

   /**
    * Activates the required handler.
    */
   protected void activateHandlers() {
      if (isEditable()) {
         fContentAssistActivation = fHandlerService.activateHandler(ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS, fContentAssistHandler);
         fUndoActivation = fHandlerService.activateHandler(IWorkbenchCommandConstants.EDIT_UNDO, fUndoHandler);
         fRedoActivation = fHandlerService.activateHandler(IWorkbenchCommandConstants.EDIT_REDO, fRedoHandler);
      }
   }
   
   /**
    * Deactivates the used handler.
    */
   protected void deactivateHandlers() {
      if (fContentAssistActivation != null) {
         fHandlerService.deactivateHandler(fContentAssistActivation);
         fContentAssistActivation = null;
      }
      if (fUndoActivation != null) {
         fHandlerService.deactivateHandler(fUndoActivation);
         fUndoActivation = null;
      }
      if (fRedoActivation != null) {
         fHandlerService.deactivateHandler(fRedoActivation);
         fRedoActivation = null;
      }
   }
   
   /**
    * Sets the {@link IJavaDebugContentAssistContext} to use.
    * @param context The {@link IJavaDebugContentAssistContext} to use.
    */
   public void setContentAssistContext(IJavaDebugContentAssistContext context) {
      fViewer.unconfigure();
      final JavaDebugContentAssistProcessor fCompletionProcessor = new JavaDebugContentAssistProcessor(context);
      fViewer.configure(new DisplayViewerConfiguration() {
         public IContentAssistProcessor getContentAssistantProcessor() {
               return fCompletionProcessor;
         }
      });
   }
   
   /**
    * Returns the shown text.
    * @return The shown text.
    */
   public String getText() {
      return fViewer.getDocument().get();
   }
   
   /**
    * Sets the shown text.
    * @param text The shown text.
    */
   public void setText(String text) {
      fViewer.getDocument().set(text);
   }

   /**
    * Checks if the viewer is editable or not.
    * @return {@code true} editable, {@code false} read-only.
    */
   public boolean isEditable() {
      return fViewer.isEditable();
   }
   
   /**
    * Makes the viewer editable or not.
    * @param editable {@code true} editable, {@code false} read-only.
    */
   public void setEditable(boolean editable) {
      fViewer.setEditable(editable);
      decorateViewer();
   }
   
   /**
    * Returns the UI {@link Control}.
    * @return The UI {@link Control}.
    */
   public Control getControl() {
      return fViewer.getControl();
   }
}