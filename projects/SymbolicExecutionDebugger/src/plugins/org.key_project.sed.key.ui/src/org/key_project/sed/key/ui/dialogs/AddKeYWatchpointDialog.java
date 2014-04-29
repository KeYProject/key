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

package org.key_project.sed.key.ui.dialogs;


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.debug.ui.launchConfigurations.JavaMainTab;
import org.eclipse.jdt.internal.debug.ui.contentassist.IJavaDebugContentAssistContext;
import org.eclipse.jdt.internal.debug.ui.contentassist.TypeContext;
import org.eclipse.jdt.internal.ui.dialogs.FilteredTypesSelectionDialog;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;
import org.key_project.sed.key.ui.launch.JavaSnippetSourceViewer;
import org.key_project.sed.key.ui.launch.NoFormTabbedPropertySheetWidgetFactory;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * This dialog lets the user create a KeY Watchpoint, it is opened after user invocation.
 * 
 * @author Marco Drebing
 */
@SuppressWarnings("restriction")
public class AddKeYWatchpointDialog extends Dialog {

   
   /**
    * Defines the type to add the {@link KeYWatchpoint} to.
    */
   private Text typeText;
   
   /**
    * Composite to hold elements handling condition options
    */
   private Composite conditionComposite;
   
   /**
    * Editor for the condition.
    */
   private JavaSnippetSourceViewer conditionViewer;
   
   /**
    * Name of the project the type is located in.
    */
   private String projectName;
   
   /**
    * The condition for the {@link KeYWatchpoint}.
    */
   private String condition;
   
   /**
    * The selected type at the end
    */
   private IType finalType;
   
   /**
    * The type to put in the type selection field initially
    */
   private String initialType;

   /**
    * Creates a new Dialog to add a {@link KeYWatchpoint}.
    * 
    * @param parentShell the parent-shell or null to create a top-level shell
    * @param initialType the initial type for type selection
    */
   public AddKeYWatchpointDialog(Shell parentShell, String initialType) {
      super(parentShell);
      this.initialType=initialType;
   }
   
   @Override
   protected void configureShell(Shell newShell) {
      super.configureShell(newShell);
      newShell.setText("Add KeY Watchpoint");
   }

   @Override
   protected Control createDialogArea(Composite parent) {
      NoFormTabbedPropertySheetWidgetFactory widgetFactory = new NoFormTabbedPropertySheetWidgetFactory();
      //Type selection area
      Group javaGroup = widgetFactory.createGroup(parent, "Type Selection");
      javaGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      javaGroup.setLayout(new GridLayout(3, false));
      widgetFactory.createLabel(javaGroup, "&Type");
      //TextFields and Labels
      typeText = widgetFactory.createText(javaGroup, null);
      typeText.setEditable(true);
      typeText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      typeText.addModifyListener(new ModifyListener() {
          @Override
          public void modifyText(ModifyEvent e) {
             updateConditionViewerComposite();
             updateDialog();
          }
      });
      //Browse button
      Button browseTypeButton = widgetFactory.createButton(javaGroup, "&Browse", SWT.PUSH);
      browseTypeButton.addSelectionListener(new SelectionAdapter() {
          @Override
          public void widgetSelected(SelectionEvent e) {
              browseType();
          }
      });
      //condition editor
      conditionComposite = widgetFactory.createPlainComposite(parent, SWT.NONE);
      GridLayout conditionCompositeLayout = new GridLayout(2, false);
      conditionComposite.setLayout(conditionCompositeLayout);
      conditionComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      Label conditionLabel = widgetFactory.createLabel(conditionComposite, "C&ondition");
      conditionLabel.setLayoutData(new GridData(GridData.BEGINNING, GridData.BEGINNING, false, false));
      int conditionViewerCompositeStyle = SWT.BORDER;
      conditionViewerCompositeStyle |= SWT.V_SCROLL | SWT.H_SCROLL;
      conditionViewer = new JavaSnippetSourceViewer(conditionComposite, conditionViewerCompositeStyle);
      conditionViewer.setEditable(true);
      conditionComposite.setEnabled(false);
      conditionViewer.addPropertyChangeListener(JavaSnippetSourceViewer.PROP_TEXT, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent e) {
            updateDialog();
         }
      });
      return parent;
   }
   
   @Override
   public void create() {
      super.create();
      this.setBlockOnOpen(true);
      Button okButton = getButton(IDialogConstants.OK_ID);
      okButton.setEnabled(false);
      if(initialType!=null){
         typeText.setText(initialType);
      }
   }
   
   @Override
   protected Point getInitialSize() {
      return new Point(400, 300);
   }
   
   /**
    * <p>
    * Opens the dialog to select a Java type ({@link IType}).
    * </p>
    * <p>
    * The implementation is oriented at {@link JavaMainTab#handleSearchButtonSelected()}.
    * </p>
    */
   public void browseType() {
       try {
          IJavaProject selectedProject = getJavaProject();
          IJavaElement[] elements;
          if (selectedProject != null && selectedProject.exists()) {
              elements = new IJavaElement[] {selectedProject};
          }
          else {
              elements = JDTUtil.getAllJavaProjects();
          }
          if (elements == null) {
              elements = new IJavaElement[] {};
          }
          IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(elements, IJavaSearchScope.SOURCES|IJavaSearchScope.REFERENCED_PROJECTS|IJavaSearchScope.APPLICATION_LIBRARIES);
           FilteredTypesSelectionDialog resourceSelectionDialog = new FilteredTypesSelectionDialog(WorkbenchUtil.getActiveShell(), false, null,searchScope , IJavaSearchConstants.CLASS_AND_INTERFACE);
              resourceSelectionDialog.setInitialPattern(typeText.getText());
              resourceSelectionDialog.setTitle("Select class for KeY Watchpoint");
           if (resourceSelectionDialog.open() == FilteredTypesSelectionDialog.OK) {
               Object[] results = resourceSelectionDialog.getResult();    
               if (results != null && results.length >= 1 && results[0] instanceof IType) {
                   IType type = (IType)results[0];
                   projectName = type.getJavaProject().getElementName();
                   typeText.setText(type.getFullyQualifiedName());
               }
           }
       }
       catch (Exception e) {
           LogUtil.getLogger().logError(e);
           LogUtil.getLogger().openErrorDialog(getShell(), e);
       }
   }
   

   /**
    * Returns the currently selected Java type ({@link IType}) or {@code null} if no one is selected.
    * @return The currently selected Java type ({@link IType}) or {@code null} if no one is selected.
    */
   protected IType getType() {
       try {
           String text = typeText.getText().trim();
           if (!text.isEmpty()) {
               IJavaProject project = getJavaProject();
               if (project != null) {
                   return project.findType(text);
               }
               else {
                  IType type = null;
                  for(IJavaProject projectIter : JDTUtil.getAllJavaProjects()){
                     type = projectIter.findType(text);
                  }
                   return type;
               }
           }
           else {
               return null;
           }
       }
       catch (JavaModelException e) {
           return null;
       }
   }

   
   protected IJavaProject getJavaProject() {
      return JDTUtil.getJavaProject(projectName);
  }
   
   
   /**
    * Updates the precondition viewer composite by setting the
    * correct context for content assistant.
    */
   protected void updateConditionViewerComposite() {
      IJavaDebugContentAssistContext context = null;
      if (getType() == null) {
         conditionComposite.setEnabled(false);
      }else{
         context = new TypeContext(getType(), -1);
         conditionComposite.setEnabled(true);
         conditionViewer.setContentAssistContext(context);
      }
   }

   /**
    * @return the condition entered by the user
    */
   public String getCondition() {
      return condition;
   }

   /**
    * updates the dialog area
    */
   protected void updateDialog() {
      Button okButton = getButton(IDialogConstants.OK_ID);
      if(getType()!=null&&conditionViewer.getText()!=null&&!conditionViewer.getText().trim().equals("")){
         okButton.setEnabled(true);
         condition = conditionViewer.getText().trim();
         finalType = getType();
      }else{
         okButton.setEnabled(false);
      }
   }

   /**
    * @return the selected type
    */
   public IType getFinalType() {
      return finalType;
   }
}