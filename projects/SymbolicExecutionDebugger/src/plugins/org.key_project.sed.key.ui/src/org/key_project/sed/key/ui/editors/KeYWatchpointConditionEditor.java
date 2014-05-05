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

package org.key_project.sed.key.ui.editors;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.internal.debug.ui.JDIDebugUIPlugin;
import org.eclipse.jdt.internal.debug.ui.breakpoints.AbstractJavaBreakpointEditor;
import org.eclipse.jdt.internal.debug.ui.contentassist.IJavaDebugContentAssistContext;
import org.eclipse.jdt.internal.debug.ui.contentassist.TypeContext;
import org.eclipse.jdt.internal.debug.ui.propertypages.PropertyPageMessages;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;
import org.key_project.sed.key.ui.launch.JavaSnippetSourceViewer;
import org.key_project.sed.key.ui.launch.NoFormTabbedPropertySheetWidgetFactory;

/**
 * This editor is part of the DetailPAne that is displayed for KeY Watchpoints.
 * 
 * @author Marco Drebing
 */
@SuppressWarnings("restriction")
public class KeYWatchpointConditionEditor extends AbstractJavaBreakpointEditor{
   
   /**
    * composite holding all relevant elements
    */
   private Composite conditionComposite;
   
   /**
    * The area to edit the condition in
    */
   private JavaSnippetSourceViewer conditionViewer;
   
   /**
    * The {@link KeYWatchpoint} this editor is associated with.
    */
   private KeYWatchpoint watchpoint;
   
   /**
    * Defines that a default contract will be generated.
    */
   private Button suspendOnTrue;
   
   /**
    * Defines that one existing contract will be used.
    */
   private Button suspendOnSatisfiable;

   @Override
   public Control createControl(Composite parent) {
      NoFormTabbedPropertySheetWidgetFactory widgetFactory = new NoFormTabbedPropertySheetWidgetFactory();
      
      //suspendontrue radio button
      Composite suspendOnComposite = widgetFactory.createPlainComposite(parent, SWT.NONE);
      suspendOnComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      suspendOnComposite.setLayout(new GridLayout(2, false));
      suspendOnTrue = widgetFactory.createButton(suspendOnComposite, "Suspend &on true", SWT.RADIO);
      suspendOnTrue.setEnabled(true);
      suspendOnTrue.addSelectionListener(new SelectionAdapter() {
          @Override
          public void widgetSelected(SelectionEvent e) {
              if (suspendOnTrue.getSelection()) {
                 setDirty(true);
              }
          }
      });
      //suspendonsatisfiable radio button
      suspendOnSatisfiable = widgetFactory.createButton(suspendOnComposite, "Suspend &on satisfiable", SWT.RADIO);
      suspendOnSatisfiable.setEnabled(true);
      suspendOnSatisfiable.addSelectionListener(new SelectionAdapter() {
          @Override
          public void widgetSelected(SelectionEvent e) {
              if (suspendOnSatisfiable.getSelection()) {
                 setDirty(true);
              }
          }
      });
      //condition editor area
      conditionComposite = widgetFactory.createPlainComposite(parent, SWT.NONE);
      GridLayout conditionCompositeLayout = new GridLayout(2, false);
      conditionComposite.setLayout(conditionCompositeLayout);
      conditionComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      Label preconditionLabel = widgetFactory.createLabel(conditionComposite, "C&ondition");
      preconditionLabel.setLayoutData(new GridData(GridData.BEGINNING, GridData.BEGINNING, false, false));
      int preconditionViewerCompositeStyle = SWT.BORDER;
      preconditionViewerCompositeStyle |= SWT.V_SCROLL | SWT.H_SCROLL;
      conditionViewer = new JavaSnippetSourceViewer(conditionComposite, preconditionViewerCompositeStyle);
      conditionViewer.setEditable(true);
      conditionComposite.setEnabled(false);
      conditionViewer.addPropertyChangeListener(JavaSnippetSourceViewer.PROP_TEXT, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent e) {
            setDirty(true);
         }
      });
      if (conditionViewer.getDecoractionImage() != null) {
         conditionCompositeLayout.horizontalSpacing += conditionViewer.getDecoractionImage().getImageData().width;
      }
      return parent;
   }

   @Override
   public void setFocus() {
      conditionViewer.getControl().setFocus();
   }

   @Override
   public void doSave() throws CoreException {
      if (watchpoint != null && isDirty()) {
         if (conditionViewer.getText().trim().length() != 0) {
            watchpoint.setCondition(conditionViewer.getText().trim());
            watchpoint.setSuspendOnTrue(suspendOnTrue.getSelection());
         }
      }
      setDirty(false);
   }

   @Override
   public IStatus getStatus() {
      if (watchpoint != null) {
            if (conditionViewer.getText().trim().length() == 0) {
               return new Status(IStatus.ERROR, JDIDebugUIPlugin.getUniqueIdentifier(),  PropertyPageMessages.BreakpointConditionEditor_1);
            }
      }
      return Status.OK_STATUS;
   }

   @Override
   public Object getInput() {
      return watchpoint;
   }

   @Override
   public void setInput(Object breakpoint) throws CoreException {
      try{
         suppressPropertyChanges(true);
         if (breakpoint instanceof KeYWatchpoint) {
            setBreakpoint((KeYWatchpoint)breakpoint);
         } else {
            setBreakpoint(null);
         }
      }finally{
         suppressPropertyChanges(false);
      }
   }
   

   
   /**
    * Disposes this editor and its controls. Once disposed, the editor can no
    * longer be used.
    */
   protected void dispose() {
      super.dispose();
      conditionViewer.dispose();   
   }

   /**
    * Sets all values according to the ones saved in the watchpoint
    * 
    * @param watchpoint that holds the values
    * @throws CoreException
    */
   private void setBreakpoint(KeYWatchpoint watchpoint) throws CoreException {
      if(watchpoint!=null){
         IJavaDebugContentAssistContext context = new TypeContext(watchpoint.getType(), -1);
         this.watchpoint = watchpoint;
         conditionComposite.setEnabled(true);
         suspendOnTrue.setEnabled(true);
         suspendOnSatisfiable.setEnabled(true);
         conditionViewer.setContentAssistContext(context);
         conditionViewer.setText(watchpoint.getCondition());
         suspendOnTrue.setSelection(watchpoint.isSuspendOnTrue());
         suspendOnSatisfiable.setSelection(!watchpoint.isSuspendOnTrue());
      }else{
         conditionComposite.setEnabled(false);
         suspendOnTrue.setEnabled(false);
         suspendOnSatisfiable.setEnabled(false);
      }
   }

}