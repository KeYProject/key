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

package org.key_project.sed.key.ui.visualization.object_diagram.editor;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.CustomContext;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Slider;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.ide.IDE;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.key.ui.visualization.object_diagram.feature.GenerateObjectDiagramFromMemoryLayoutCustomFeature;
import org.key_project.sed.ui.visualization.object_diagram.editor.ObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.editor.ReadonlyObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.perspective.StateVisualizationPerspectiveFactory;
import org.key_project.sed.ui.visualization.object_diagram.provider.ObjectDiagramTypeProvider;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.NonPersistableDiagramEditorInput;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.job.AbstractDependingOnObjectsJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;

/**
 * Read-only {@link ObjectDiagramEditor} specialized to show memory layouts.
 * @author Martin Hentschel
 */
public class MemoryLayoutDiagramEditor extends ReadonlyObjectDiagramEditor {
   /**
    * The ID of this editor.
    */
   public static final String EDITOR_ID = "org.key_project.sed.key.ui.MemoryLayoutDiagramEditor";
   /**
    * Radio {@link Button} to show initial memory layouts.
    */
   private Button initialLayoutButton;
   
   /**
    * Radio {@link Button} to show current memory layouts.
    */
   private Button currentLayoutButton;

   /**
    * Slider to select memory layouts.
    */
   private Slider slider;
   
   /**
    * {@link Button} to open a dialog to select a memory layout.
    */
   private Button selectLayoutButton;
   
   /**
    * Shows the equivalence classes of the current memory layout.
    */
   private Text equivalenceClassesText;
   
   /**
    * The {@link IExecutionStateNode} which provides the memory layouts.
    */
   private IExecutionStateNode<?> node;
   
   /**
    * The currently shown {@link ISymbolicLayout}.
    */
   private ISymbolicLayout shownLayout;
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   public void createPartControl(Composite parent) {
      // Create root
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
      // Create diagram
      Composite diagramComposite = new Composite(root, SWT.NONE);
      diagramComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      diagramComposite.setLayout(new FillLayout());
      super.createPartControl(diagramComposite);
      // Create layout controls
      Composite layoutComposite = new Composite(root, SWT.NONE);  
      layoutComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      layoutComposite.setLayout(new GridLayout(5, false));
      initialLayoutButton = new Button(layoutComposite, SWT.RADIO);
      initialLayoutButton.setText("&Initial");
      initialLayoutButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (initialLayoutButton.getSelection()){
               showLayout(slider.getSelection(), true);
            }
         }
      });
      currentLayoutButton = new Button(layoutComposite, SWT.RADIO);
      currentLayoutButton.setText("&Current");
      currentLayoutButton.setSelection(true);
      currentLayoutButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (currentLayoutButton.getSelection()){
               showLayout(slider.getSelection(), false);
            }
         }
      });
      slider = new Slider(layoutComposite, SWT.HORIZONTAL);
      slider.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            showLayout(slider.getSelection(), initialLayoutButton.getSelection());
         }
      });
      selectLayoutButton = new Button(layoutComposite, SWT.PUSH);
      selectLayoutButton.setText("&...");
      selectLayoutButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            openSelectLayoutsDialog();
         }
      });
      equivalenceClassesText = new Text(layoutComposite, SWT.BORDER);
      equivalenceClassesText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      equivalenceClassesText.setEditable(false);
      setLayoutControlsEnabled(false);
   }

   /**
    * Enables or disables the layout controls.
    * @param enabled {@code true} set enabled, {@code false} set disabled.
    */
   protected void setLayoutControlsEnabled(boolean enabled) {
      initialLayoutButton.setEnabled(enabled);
      currentLayoutButton.setEnabled(enabled);
      slider.setEnabled(enabled);
      selectLayoutButton.setEnabled(enabled);
   }
   
   /**
    * Generates an object diagram for the first layout of the given {@link IKeYSEDDebugNode}.
    * @param node {@link IKeYSEDDebugNode} to generate layout for.
    */
   public void generateMemoryLayoutsDiagram(IKeYSEDDebugNode<?> node) {
      setLayoutControlsEnabled(false);
      SWTUtil.setText(equivalenceClassesText, null);
      if (node != null && node.getExecutionNode() instanceof IExecutionStateNode<?>) {
         this.node = (IExecutionStateNode<?>)node.getExecutionNode();
         new AbstractDependingOnObjectsJob("Computing memory layouts.", this) {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  SWTUtil.checkCanceled(monitor);
                  initLayoutControls();
                  return Status.OK_STATUS;
               }
               catch (OperationCanceledException e) {
                  return Status.CANCEL_STATUS;
               }
               catch (Exception e) {
                  return LogUtil.getLogger().createErrorStatus(e);
               }
            }
         }.schedule();
      }
      else {
         this.node = null;
      }
   }
   
   /**
    * Initializes the layout controls with the content provided by the {@link IExecutionStateNode}.
    * @throws ProofInputException Occurred Exception.
    */
   protected void initLayoutControls() throws ProofInputException {
      final int layoutsCount = this.node.getLayoutsCount();
      if (layoutsCount >= 1 && !slider.isDisposed()) {
         slider.getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               initialLayoutButton.setSelection(false);
               currentLayoutButton.setSelection(true);
               slider.setValues(0, 0, layoutsCount, 1, 1, 1);
               setLayoutControlsEnabled(true);
               showLayout(0, false);
            }
         });
      }
   }
   
   /**
    * Shows the memory layout at the given index in the given mode.
    * @param index The memory layout index.
    * @param initial The memory layout mode ({@code true} = initial, {@code false} = current).
    */
   protected void showLayout(final int index, final boolean initial) {
      new AbstractDependingOnObjectsJob("Show " + (initial ? "initial" : "current") + " memory layout " + index + ".", this) {
         @Override
         protected IStatus run(IProgressMonitor monitor) {
            try {
               SWTUtil.checkCanceled(monitor);
               final ISymbolicLayout toShow = initial ? 
                                                     node.getInitialLayout(index) : 
                                                     node.getCurrentLayout(index);
               if (shownLayout != toShow) {
                  shownLayout = toShow;
                  if (!equivalenceClassesText.isDisposed()) {
                     equivalenceClassesText.getDisplay().syncExec(new Runnable() {
                        @Override
                        public void run() {
                           initialLayoutButton.setSelection(initial);
                           currentLayoutButton.setSelection(!initial);
                           slider.setSelection(index);
                           if (toShow != null && toShow.getEquivalenceClasses() != null) {
                              SWTUtil.setText(equivalenceClassesText, toShow.getEquivalenceClasses().toString());
                           }
                           else {
                              SWTUtil.setText(equivalenceClassesText, null);
                           }
                        }
                     });
                  }
                  GenerateObjectDiagramFromMemoryLayoutCustomFeature feature = new GenerateObjectDiagramFromMemoryLayoutCustomFeature(getDiagramTypeProvider().getFeatureProvider());
                  ICustomContext context = new CustomContext();
                  context.putProperty(GraphitiUtil.CONTEXT_PROPERTY_MONITOR, monitor);
                  context.putProperty(GenerateObjectDiagramFromMemoryLayoutCustomFeature.PROPERTY_MEMORY_LAYOUT, toShow);
                  executeFeature(feature, context);
               }
               return Status.OK_STATUS;
            }
            catch (OperationCanceledException e) {
               return Status.CANCEL_STATUS;
            }
            catch (Exception e) {
               return LogUtil.getLogger().createErrorStatus(e);
            }
         }
      }.schedule();
   }

   /**
    * Opens a dialog to select memory layouts.
    */
   public void openSelectLayoutsDialog() {
      try {
         // Collect equivalence classes of memory layouts.
         Object[] elements = new Object[node.getLayoutsCount()];
         for (int i = 0; i < elements.length; i++) {
            elements[i] = node.getLayoutsEquivalenceClasses(i);
         }
         // Open dialog
         ElementListSelectionDialog dialog = new ElementListSelectionDialog(getSite().getShell(), new LabelProvider());
         dialog.setTitle("Memory Layout Selection");
         dialog.setMessage("Select a memory layout.");
         dialog.setElements(elements);
         if (ElementListSelectionDialog.OK == dialog.open()) {
            Object result = dialog.getFirstResult();
            int index = ArrayUtil.indexOf(elements, result);
            slider.setSelection(index);
            showLayout(index, initialLayoutButton.getSelection());
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
      }
   }

   /**
    * Opens a {@link MemoryLayoutDiagramEditor}.
    * @param page The {@link IWorkbenchPage} to open editor in..
    * @param diagramName The name of the diagram.
    * @param uniqueId A unique ID to identify the opened file.
    * @return The opened {@link MemoryLayoutDiagramEditor} or the returned one if a file with the given ID is already opened.
    * @throws PartInitException Occurred Exception.
    */
   public static MemoryLayoutDiagramEditor openEditor(IWorkbenchPage page, String diagramName, String uniqueId) throws PartInitException {
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
                                              MemoryLayoutDiagramEditor.EDITOR_ID);
      if (ObjectDiagramUtil.shouldSwitchToStateVisualizationPerspective(page)) {
         WorkbenchUtil.openPerspective(StateVisualizationPerspectiveFactory.PERSPECTIVE_ID);
      }
      Assert.isTrue(editorPart instanceof MemoryLayoutDiagramEditor);
      return (MemoryLayoutDiagramEditor)editorPart;
   }
}