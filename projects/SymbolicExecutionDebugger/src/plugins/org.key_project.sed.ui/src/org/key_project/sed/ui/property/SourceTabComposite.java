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

package org.key_project.sed.ui.property;

import java.io.File;

import org.eclipse.core.resources.IResource;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * This composite provides the content shown in {@link SourcePropertySection}
 * and in {@code GraphitiSourcePropertySection}.
 * @author Martin Hentschel
 */
public class SourceTabComposite extends Composite {
   /**
    * The currently shown {@link Composite}.
    */
   private Composite composite;

   /**
    * The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   private TabbedPropertySheetWidgetFactory factory;
 
   /**
    * The used {@link WorkbenchLabelProvider} to get {@link Image}s of {@link IResource}s.
    */
   private WorkbenchLabelProvider labelProvider = new WorkbenchLabelProvider();

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public SourceTabComposite(Composite parent, int style, TabbedPropertySheetWidgetFactory factory) {
      super(parent, style);
      this.factory = factory;
      setLayout(new FillLayout());
   }

   /**
    * Updates the shown content.
    * @param frame The {@link IStackFrame} which provides the new content.
    */
   public void updateContent(IStackFrame frame) {
      String sourceText = null;
      Image sourceIcon = null;
      String workspacePath = null;
      String localPath = null;
      int lineNumber = -1;
      int startChar = -1;
      int endChar = -1;
      if (frame != null) {
         Object source = frame.getLaunch().getSourceLocator().getSourceElement(frame);
         if (source instanceof IResource) {
            IResource resource = (IResource)source;
            sourceText = labelProvider.getText(resource);
            sourceIcon = labelProvider.getImage(resource);
            workspacePath = resource.getFullPath().toString();
            File file = ResourceUtil.getLocation(resource);
            if (file != null) {
               localPath = file.getAbsolutePath();
            }
         }
         else if (source instanceof File) {
            File file = (File)source;
            sourceText = file.getName();
            localPath = file.getAbsolutePath();
         }
         else {
            sourceText = ObjectUtil.toString(source);
         }
         try {
            lineNumber = frame.getLineNumber();
            startChar = frame.getCharStart();
            endChar = frame.getCharEnd();
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      recreateContent(sourceText, sourceIcon, workspacePath, localPath, lineNumber, startChar, endChar);
   }
   
   /**
    * Updates the shown content by recreating it.
    * @param sourceText The source text.
    * @param sourceIcon The source icon.
    * @param workspacePath The workspace path
    * @param localPath The local file system path.
    * @param lineNumber The line number.
    * @param startChar The start character.
    * @param endChar The end character.
    */
   protected void recreateContent(String sourceText,
                                  Image sourceIcon,
                                  String workspacePath,
                                  String localPath,
                                  int lineNumber,
                                  int startChar,
                                  int endChar) {
      disposeContent();
      createContent(sourceText, sourceIcon, workspacePath, localPath, lineNumber, startChar, endChar);
      layout();
   }
   
   /**
    * Disposes the currently shown content.
    */
   protected void disposeContent() {
      if (composite != null) {
         composite.setVisible(false);
         composite.dispose();
         composite = null;
      }
   }
   
   /**
    * Creates a new content which shows the given values.
    * @param sourceText The source text.
    * @param sourceIcon The source icon.
    * @param workspacePath The workspace path
    * @param localPath The local file system path.
    * @param lineNumber The line number.
    * @param startChar The start character.
    * @param endChar The end character.
    */
   protected void createContent(String sourceText,
                                Image sourceIcon,
                                String workspacePath,
                                String localPath,
                                int lineNumber,
                                int startChar,
                                int endChar) {
      composite = factory.createFlatFormComposite(this);

      final int LABEL_WIDTH = 110;
      
      Control lastControl = null;
      if (sourceText != null || sourceIcon != null) {
         CLabel sourceCLabel = factory.createCLabel(composite, sourceText);
         sourceCLabel.setImage(sourceIcon);
         FormData data = new FormData();
         data.left = new FormAttachment(0, LABEL_WIDTH);
         data.right = new FormAttachment(100, 0);
         data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
         sourceCLabel.setLayoutData(data);
         lastControl = sourceCLabel;

         CLabel sourceLabel = factory.createCLabel(composite, "Source:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(sourceCLabel, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(sourceCLabel, 0, SWT.CENTER);
         sourceLabel.setLayoutData(data);
      }
      
      if (workspacePath != null) {
         Text workspacePathText = factory.createText(composite, workspacePath);
         workspacePathText.setEditable(false);
         FormData data = new FormData();
         data.left = new FormAttachment(0, LABEL_WIDTH);
         data.right = new FormAttachment(100, 0);
         data.top = new FormAttachment(lastControl, 0, ITabbedPropertyConstants.VSPACE);
         workspacePathText.setLayoutData(data);
         lastControl = workspacePathText;
         
         CLabel workspacePathLabel = factory.createCLabel(composite, "Workspace Path:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(workspacePathText, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(workspacePathText, 0, SWT.CENTER);
         workspacePathLabel.setLayoutData(data);
      }

      if (localPath != null) {
         Text localPathText = factory.createText(composite, localPath);
         localPathText.setEditable(false);
         FormData data = new FormData();
         data.left = new FormAttachment(0, LABEL_WIDTH);
         data.right = new FormAttachment(100, 0);
         data.top = new FormAttachment(lastControl, 0, ITabbedPropertyConstants.VSPACE);
         localPathText.setLayoutData(data);
         lastControl = localPathText;
         
         CLabel localPathLabel = factory.createCLabel(composite, "File System Path:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(localPathText, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(localPathText, 0, SWT.CENTER);
         localPathLabel.setLayoutData(data);
      }

      if (lineNumber >= 0) {
         Text lineNumberText = factory.createText(composite, lineNumber + StringUtil.EMPTY_STRING);
         lineNumberText.setEditable(false);
         FormData data = new FormData();
         data.left = new FormAttachment(0, LABEL_WIDTH);
         data.right = new FormAttachment(25, 0);
         data.top = new FormAttachment(lastControl, 0, ITabbedPropertyConstants.VSPACE);
         lineNumberText.setLayoutData(data);
         lastControl = lineNumberText;
         
         CLabel lineNumberLabel = factory.createCLabel(composite, "Line Number:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(lineNumberText, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(lineNumberText, 0, SWT.CENTER);
         lineNumberLabel.setLayoutData(data);
      }

      if (startChar >= 0) {
         Text charStartText = factory.createText(composite, startChar + StringUtil.EMPTY_STRING);
         charStartText.setEditable(false);
         FormData data = new FormData();
         data.left = new FormAttachment(0, LABEL_WIDTH);
         data.right = new FormAttachment(25, 0);
         data.top = new FormAttachment(lastControl, 0, ITabbedPropertyConstants.VSPACE);
         charStartText.setLayoutData(data);
         lastControl = charStartText;
         
         CLabel charStartLabel = factory.createCLabel(composite, "Start Character:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(charStartText, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(charStartText, 0, SWT.CENTER);
         charStartLabel.setLayoutData(data);
      }

      if (endChar >= 0) {
         Text charEndText = factory.createText(composite, endChar + StringUtil.EMPTY_STRING);
         charEndText.setEditable(false);
         FormData data = new FormData();
         data.left = new FormAttachment(0, LABEL_WIDTH);
         data.right = new FormAttachment(25, 0);
         data.top = new FormAttachment(lastControl, 0, ITabbedPropertyConstants.VSPACE);
         charEndText.setLayoutData(data);
         lastControl = charEndText;
         
         CLabel charEndLabel = factory.createCLabel(composite, "End Character:");
         data = new FormData();
         data.left = new FormAttachment(0, 0);
         data.right = new FormAttachment(charEndText, -ITabbedPropertyConstants.HSPACE);
         data.top = new FormAttachment(charEndText, 0, SWT.CENTER);
         charEndLabel.setLayoutData(data);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      super.dispose();
   }
}