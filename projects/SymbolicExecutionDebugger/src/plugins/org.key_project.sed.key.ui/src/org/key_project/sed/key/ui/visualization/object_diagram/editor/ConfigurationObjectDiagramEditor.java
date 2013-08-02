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
import org.key_project.sed.key.ui.visualization.object_diagram.feature.GenerateObjectDiagramFromSymbolicConfigurationCustomFeature;
import org.key_project.sed.ui.visualization.object_diagram.editor.ObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.editor.ReadonlyObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.perspective.StateVisualizationPerspectiveFactory;
import org.key_project.sed.ui.visualization.object_diagram.provider.ObjectDiagramTypeProvider;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.NonPersistableDiagramEditorInput;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.job.AbstractWorkbenchPartJob;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;

/**
 * Read-only {@link ObjectDiagramEditor} specialized to show configurations.
 * @author Martin Hentschel
 */
public class ConfigurationObjectDiagramEditor extends ReadonlyObjectDiagramEditor {
   /**
    * The ID of this editor.
    */
   public static final String EDITOR_ID = "org.key_project.sed.key.ui.ConfigurationObjectDiagramEditor";
   /**
    * Radio {@link Button} to show initial configurations.
    */
   private Button initialConfiguration;
   
   /**
    * Radio {@link Button} to show current configurations.
    */
   private Button currentConfiguration;

   /**
    * Slider to select configurations.
    */
   private Slider slider;
   
   /**
    * {@link Button} to open a dialog to select a configuration.
    */
   private Button selectConfigurationButton;
   
   /**
    * Shows the equivalence classes of the current configuration.
    */
   private Text equivalenceClassesText;
   
   /**
    * The {@link IExecutionStateNode} which provides the configurations.
    */
   private IExecutionStateNode<?> node;
   
   /**
    * The currently shown {@link ISymbolicConfiguration}.
    */
   private ISymbolicConfiguration shownConfiguration;
   
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
      // Create configurations controls
      Composite configurationComposite = new Composite(root, SWT.NONE);  
      configurationComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      configurationComposite.setLayout(new GridLayout(5, false));
      initialConfiguration = new Button(configurationComposite, SWT.RADIO);
      initialConfiguration.setText("&Initial");
      initialConfiguration.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (initialConfiguration.getSelection()){
               showConfiguration(slider.getSelection(), true);
            }
         }
      });
      currentConfiguration = new Button(configurationComposite, SWT.RADIO);
      currentConfiguration.setText("&Current");
      currentConfiguration.setSelection(true);
      currentConfiguration.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (currentConfiguration.getSelection()){
               showConfiguration(slider.getSelection(), false);
            }
         }
      });
      slider = new Slider(configurationComposite, SWT.HORIZONTAL);
      slider.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            showConfiguration(slider.getSelection(), initialConfiguration.getSelection());
         }
      });
      selectConfigurationButton = new Button(configurationComposite, SWT.PUSH);
      selectConfigurationButton.setText("&...");
      selectConfigurationButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            openSelectConfigurationsDialog();
         }
      });
      equivalenceClassesText = new Text(configurationComposite, SWT.BORDER);
      equivalenceClassesText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      equivalenceClassesText.setEditable(false);
      setConfigurationControlsEnabled(false);
   }

   /**
    * Enables or disables the configuration controls.
    * @param enabled {@code true} set enabled, {@code false} set disabled.
    */
   protected void setConfigurationControlsEnabled(boolean enabled) {
      initialConfiguration.setEnabled(enabled);
      currentConfiguration.setEnabled(enabled);
      slider.setEnabled(enabled);
      selectConfigurationButton.setEnabled(enabled);
   }
   
   /**
    * Generates an object diagram for the first configuration of the given {@link IKeYSEDDebugNode}.
    * @param node {@link IKeYSEDDebugNode} to generate configuration for.
    */
   public void generateConfigurationsDiagram(IKeYSEDDebugNode<?> node) {
      setConfigurationControlsEnabled(false);
      SWTUtil.setText(equivalenceClassesText, null);
      if (node != null && node.getExecutionNode() instanceof IExecutionStateNode<?>) {
         this.node = (IExecutionStateNode<?>)node.getExecutionNode();
         new AbstractWorkbenchPartJob("Computing configurations.", this) {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  SWTUtil.checkCanceled(monitor);
                  initConfigurationControls();
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
    * Initializes the configuration controls with the content provided by the {@link IExecutionStateNode}.
    * @throws ProofInputException Occurred Exception.
    */
   protected void initConfigurationControls() throws ProofInputException {
      final int configurationsCount = this.node.getConfigurationsCount();
      if (configurationsCount >= 1 && !slider.isDisposed()) {
         slider.getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               initialConfiguration.setSelection(false);
               currentConfiguration.setSelection(true);
               slider.setValues(0, 0, configurationsCount, 1, 1, 1);
               setConfigurationControlsEnabled(true);
               showConfiguration(0, false);
            }
         });
      }
   }
   
   /**
    * Shows the configuration at the given index in the given mode.
    * @param index The configuration index.
    * @param initial The configuration mode ({@code true} = initial, {@code false} = current).
    */
   protected void showConfiguration(final int index, final boolean initial) {
      new AbstractWorkbenchPartJob("Show " + (initial ? "initial" : "current") + " configuration " + index + ".", this) {
         @Override
         protected IStatus run(IProgressMonitor monitor) {
            try {
               SWTUtil.checkCanceled(monitor);
               final ISymbolicConfiguration toShow = initial ? 
                                                     node.getInitialConfiguration(index) : 
                                                     node.getCurrentConfiguration(index);
               if (shownConfiguration != toShow) {
                  shownConfiguration = toShow;
                  if (!equivalenceClassesText.isDisposed()) {
                     equivalenceClassesText.getDisplay().syncExec(new Runnable() {
                        @Override
                        public void run() {
                           initialConfiguration.setSelection(initial);
                           currentConfiguration.setSelection(!initial);
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
                  GenerateObjectDiagramFromSymbolicConfigurationCustomFeature feature = new GenerateObjectDiagramFromSymbolicConfigurationCustomFeature(getDiagramTypeProvider().getFeatureProvider());
                  ICustomContext context = new CustomContext();
                  context.putProperty(GraphitiUtil.CONTEXT_PROPERTY_MONITOR, monitor);
                  context.putProperty(GenerateObjectDiagramFromSymbolicConfigurationCustomFeature.PROPERTY_SYMBOLIC_CONFIGURATION, toShow);
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
    * Opens a dialog to select configurations.
    */
   public void openSelectConfigurationsDialog() {
      try {
         // Collect equivalence classes of configurations.
         Object[] elements = new Object[node.getConfigurationsCount()];
         for (int i = 0; i < elements.length; i++) {
            elements[i] = node.getConfigurationsEquivalenceClasses(i);
         }
         // Open dialog
         ElementListSelectionDialog dialog = new ElementListSelectionDialog(getSite().getShell(), new LabelProvider());
         dialog.setTitle("Configuration Selection");
         dialog.setMessage("Select a configuration.");
         dialog.setElements(elements);
         if (ElementListSelectionDialog.OK == dialog.open()) {
            Object result = dialog.getFirstResult();
            int index = ArrayUtil.indexOf(elements, result);
            slider.setSelection(index);
            showConfiguration(index, initialConfiguration.getSelection());
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
      }
   }

   /**
    * Opens a {@link ConfigurationObjectDiagramEditor}.
    * @param page The {@link IWorkbenchPage} to open editor in..
    * @param diagramName The name of the diagram.
    * @param uniqueId A unique ID to identify the opened file.
    * @return The opened {@link ConfigurationObjectDiagramEditor} or the returned one if a file with the given ID is already opened.
    * @throws PartInitException Occurred Exception.
    */
   public static ConfigurationObjectDiagramEditor openEditor(IWorkbenchPage page, String diagramName, String uniqueId) throws PartInitException {
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
                                              ConfigurationObjectDiagramEditor.EDITOR_ID);
      if (ObjectDiagramUtil.shouldSwitchToStateVisualizationPerspective(page)) {
         WorkbenchUtil.openPerspective(StateVisualizationPerspectiveFactory.PERSPECTIVE_ID);
      }
      Assert.isTrue(editorPart instanceof ConfigurationObjectDiagramEditor);
      return (ConfigurationObjectDiagramEditor)editorPart;
   }
}