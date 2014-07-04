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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.debug.ui.launchConfigurations.JavaMainTab;
import org.eclipse.jdt.internal.debug.ui.contentassist.IJavaDebugContentAssistContext;
import org.eclipse.jdt.internal.debug.ui.contentassist.TypeContext;
import org.eclipse.jdt.internal.debug.ui.launcher.AbstractJavaMainTab;
import org.eclipse.jdt.internal.debug.ui.launcher.DebugTypeSelectionDialog;
import org.eclipse.jdt.ui.JavaElementLabelProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.key4eclipse.common.ui.dialog.ContractSelectionDialog;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.launch.KeYLaunchSettings;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.jdt.AllOperationsSearchEngine;
import org.key_project.sed.key.ui.jdt.AllTypesSearchEngine;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.FileExtensionViewerFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithProgressAndResult;
import org.key_project.util.java.thread.IRunnableWithProgressAndResult;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Contains the controls to define a project, type, method and a contract to debug.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class MainLaunchConfigurationComposite extends AbstractTabbedPropertiesAndLaunchConfigurationTabComposite {
   /**
    * Radio button to start a new debug session.
    */
   private Button newDebugSessionButton;
   
   /**
    * Radio button to continue an existing debug session (*.proof file).
    */
   private Button continueDebugSessionButton;
   
   /**
    * Shows {@link #newDebugSessionComposite} or {@link #continueDebugSessionComposite}.
    */
   private Composite newOrContinueComposite;
   
   /**
    * {@link StackLayout} used in {@link #newOrContinueComposite}.
    */
   private StackLayout newOrContinueCompositeLayout;
   
   /**
    * Contains the UI controls to start a new debug session.
    */
   private Composite newDebugSessionComposite;
   
   /**
    * Contains the UI controls to continue an existing debug session.
    */
   private Composite continueDebugSessionComposite;
   
   /**
    * Defines the proof file to continue.
    */
   private Text proofFileText;
   
   /**
    * Defines the project that contains the type to debug.
    */
   private Text projectText;
   
   /**
    * Defines the type to debug.
    */
   private Text typeText;
   
   /**
    * Defines the method to debug.
    */
   private Text methodText;
   
   /**
    * Defines to execute the complete method body.
    */
   private Button executeMethodBodyButton;
   
   /**
    * Defines to execute a selected range within the method body.
    */
   private Button executeMethodRangeButton;
   
   /**
    * The start line.
    */
   private Text startLineText;
   
   /**
    * The start column.
    */
   private Text startColumnText;
   
   /**
    * The end line.
    */
   private Text endLineText;
   
   /**
    * The end column.
    */
   private Text endColumnText;
   
   /**
    * Defines that a default contract will be generated.
    */
   private Button useGeneratedContractButton;
   
   /**
    * Defines that one existing contract will be used.
    */
   private Button useExistingContractButton;

   /**
    * Defines the existing contract to use.
    */
   private Text existingContractText;
   
   /**
    * Last loaded {@link InitConfig}.
    */
   private InitConfig initConfig;
   
   /**
    * The name of the project that is loaded in {@link #initConfig}.
    */
   private String initConfigProject;
   
   /**
    * {@link Button} to browse a contract.
    */
   private Button browseContractButton;
   
   /**
    * Edits the custom precondition.
    */
   private JavaSnippetSourceViewer preconditionViewer;
   
   /**
    * Contains the controls to define an existing contract.
    */
   private Composite existingContractComposite;
   
   /**
    * Shows the controls to define a precondition.
    */
   private Composite preconditionComposite;
   
   /**
    * Shows {@link #preconditionComposite} if {@link #useGeneratedContractButton}
    * is selected or {@link #existingContractComposite} if {@link #useExistingContractButton} is selected.
    */
   private Composite contractComposite;
   
   /**
    * {@link StackLayout} used in {@link #contractComposite}.
    */
   private StackLayout contractCompositeLayout;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @param parentTab An optional {@link AbstractTabbedPropertiesAndLaunchConfigurationTab} to make this {@link Composite} editable.
    * @param widgetFactory An optional {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public MainLaunchConfigurationComposite(Composite parent, 
                                           int style, 
                                           AbstractTabbedPropertiesAndLaunchConfigurationTab parentTab,
                                           TabbedPropertySheetWidgetFactory widgetFactory) {
      super(parent, style, parentTab);
      setLayout(new FillLayout());
      if (widgetFactory == null) {
         widgetFactory = new NoFormTabbedPropertySheetWidgetFactory();
      }
      // Content composite
      Composite composite = widgetFactory.createFlatFormComposite(this);
      composite.setLayout(new GridLayout(1, false));
      // New continue radio button composite
      Composite newOrConitnueRadioButtonComposite = widgetFactory.createComposite(composite);
      newOrConitnueRadioButtonComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      newOrConitnueRadioButtonComposite.setLayout(new GridLayout(2, false));
      newDebugSessionButton = widgetFactory.createButton(newOrConitnueRadioButtonComposite, "New debug session", SWT.RADIO);
      newDebugSessionButton.setEnabled(isEditable());
      newDebugSessionButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (newDebugSessionButton.getSelection()) {
               updateShownSessionComposite();
               updateLaunchConfigurationDialog();
            }
         }
      });
      continueDebugSessionButton = widgetFactory.createButton(newOrConitnueRadioButtonComposite, "Continue debug session (*." + KeYUtil.PROOF_FILE_EXTENSION + " file)", SWT.RADIO);
      continueDebugSessionButton.setEnabled(isEditable());
      continueDebugSessionButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (continueDebugSessionButton.getSelection()) {
               updateShownSessionComposite();
               updateLaunchConfigurationDialog();
            }
         }
      });
      // New or continue composite
      newOrContinueCompositeLayout = new StackLayout();
      newOrContinueComposite = widgetFactory.createComposite(composite);
      newOrContinueComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      newOrContinueComposite.setLayout(newOrContinueCompositeLayout);
      // Continue debug session composite
      continueDebugSessionComposite = widgetFactory.createComposite(newOrContinueComposite);
      continueDebugSessionComposite.setLayout(new GridLayout(1, false));
      // New debug session composite
      newDebugSessionComposite = widgetFactory.createComposite(newOrContinueComposite);
      newDebugSessionComposite.setLayout(new GridLayout(1, false));
      newOrContinueCompositeLayout.topControl = newDebugSessionComposite;
      // Existing file group
      Group existingFileGroup = widgetFactory.createGroup(continueDebugSessionComposite, "Existing *." + KeYUtil.PROOF_FILE_EXTENSION + " file");
      existingFileGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      existingFileGroup.setLayout(new GridLayout(isEditable() ? 3 : 2, false));
      widgetFactory.createLabel(existingFileGroup, "&File");
      proofFileText = widgetFactory.createText(existingFileGroup, null);
      proofFileText.setEditable(isEditable());
      proofFileText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      proofFileText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      if (isEditable()) {
         Button browseProofFileButton = widgetFactory.createButton(existingFileGroup, "B&rowse", SWT.PUSH);
         browseProofFileButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 browseProofFile();
             }
         });
      }
      // Project
      Group projectGroup = widgetFactory.createGroup(newDebugSessionComposite, "Project");
      projectGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      projectGroup.setLayout(new GridLayout(isEditable() ? 3 : 2, false));
      widgetFactory.createLabel(projectGroup, "&Project name");
      projectText = widgetFactory.createText(projectGroup, null);
      projectText.setEditable(isEditable());
      projectText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      projectText.addModifyListener(new ModifyListener() {
          @Override
          public void modifyText(ModifyEvent e) {
              unsetInitConfig();
              updateLaunchConfigurationDialog();
          }
      });
      if (isEditable()) {
         Button browseProjectButton = widgetFactory.createButton(projectGroup, "B&rowse", SWT.PUSH);
         browseProjectButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 browseProject();
             }
         });
      }
      // Java
      Group javaGroup = widgetFactory.createGroup(newDebugSessionComposite, "Java");
      javaGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      javaGroup.setLayout(new GridLayout(isEditable() ? 3 : 2, false));
      widgetFactory.createLabel(javaGroup, "&Type");
      typeText = widgetFactory.createText(javaGroup, null);
      typeText.setEditable(isEditable());
      typeText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      typeText.addModifyListener(new ModifyListener() {
          @Override
          public void modifyText(ModifyEvent e) {
              updateLaunchConfigurationDialog();
          }
      });
      if (isEditable()) {
         Button browseTypeButton = widgetFactory.createButton(javaGroup, "&Browse", SWT.PUSH);
         browseTypeButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 browseType();
             }
         });
      }
      widgetFactory.createLabel(javaGroup, "&Method");
      methodText = widgetFactory.createText(javaGroup, null);
      methodText.setEditable(isEditable());
      methodText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      methodText.addModifyListener(new ModifyListener() {
          @Override
          public void modifyText(ModifyEvent e) {
              updateLaunchConfigurationDialog();
              updatePreconditionViewerComposite();
          }
      });
      if (isEditable()) {
         Button browseMethodButton = widgetFactory.createButton(javaGroup, "Bro&wse", SWT.PUSH);
         browseMethodButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 browseMethod();
             }
         });
      }
      widgetFactory.createLabel(javaGroup, "Range");
      Composite rangeComposite = widgetFactory.createPlainComposite(javaGroup, SWT.NONE);
      rangeComposite.setLayoutData(new GridData(GridData.BEGINNING, GridData.BEGINNING, true, true, 2, 1));
      rangeComposite.setLayout(new GridLayout(9, false));
      executeMethodBodyButton = widgetFactory.createButton(rangeComposite, "Complete method bod&y", SWT.RADIO);
      executeMethodBodyButton.setEnabled(isEditable());
      executeMethodBodyButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateRangeTextEditableState();
            updateLaunchConfigurationDialog();
         }
      });
      executeMethodRangeButton = widgetFactory.createButton(rangeComposite, "R&ange from", SWT.RADIO);
      executeMethodRangeButton.setEnabled(isEditable());
      executeMethodRangeButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateRangeTextEditableState();
            updateLaunchConfigurationDialog();
         }
      });
      startLineText = widgetFactory.createText(rangeComposite, null);
      GridData fixedSizeGridData = new GridData(GridData.CENTER, GridData.CENTER, false, false);
      fixedSizeGridData.widthHint = 50;
      fixedSizeGridData.grabExcessHorizontalSpace = false;
      startLineText.setLayoutData(fixedSizeGridData);
      startLineText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
             updateLaunchConfigurationDialog();
         }
      });
      widgetFactory.createLabel(rangeComposite, ":");
      startColumnText = widgetFactory.createText(rangeComposite, null);
      startColumnText.setLayoutData(fixedSizeGridData);
      startColumnText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
             updateLaunchConfigurationDialog();
         }
      });
      widgetFactory.createLabel(rangeComposite, "to");
      endLineText = widgetFactory.createText(rangeComposite, null);
      endLineText.setLayoutData(fixedSizeGridData);
      endLineText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
             updateLaunchConfigurationDialog();
         }
      });
      widgetFactory.createLabel(rangeComposite, ":");
      endColumnText = widgetFactory.createText(rangeComposite, null);
      endColumnText.setLayoutData(fixedSizeGridData);
      endColumnText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
             updateLaunchConfigurationDialog();
         }
      });
      // Verification
      Group verificationGroup = widgetFactory.createGroup(newDebugSessionComposite, "Verification");
      verificationGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      verificationGroup.setLayout(new GridLayout(1, false));
      Composite usedContractComposite = widgetFactory.createPlainComposite(verificationGroup, SWT.NONE);
      usedContractComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      usedContractComposite.setLayout(new GridLayout(2, false));
      useGeneratedContractButton = widgetFactory.createButton(usedContractComposite, "Use &generated contract", SWT.RADIO);
      useGeneratedContractButton.setEnabled(isEditable());
      useGeneratedContractButton.addSelectionListener(new SelectionAdapter() {
          @Override
          public void widgetSelected(SelectionEvent e) {
              if (useGeneratedContractButton.getSelection()) {
                  updateLaunchConfigurationDialog();
                  updateShownContractComposite();
              }
          }
      });
      useExistingContractButton = widgetFactory.createButton(usedContractComposite, "Use &existing contract", SWT.RADIO);
      useExistingContractButton.setEnabled(isEditable());
      useExistingContractButton.addSelectionListener(new SelectionAdapter() {
          @Override
          public void widgetSelected(SelectionEvent e) {
              if (useExistingContractButton.getSelection()) {
                  updateLaunchConfigurationDialog();
                  updateShownContractComposite();
              }
          }
      });
      
      contractCompositeLayout = new StackLayout();
      contractComposite = widgetFactory.createPlainComposite(verificationGroup, SWT.NONE);
      contractComposite.setLayout(contractCompositeLayout);
      contractComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      
      existingContractComposite = widgetFactory.createPlainComposite(contractComposite, SWT.NONE);
      existingContractComposite.setLayout(new GridLayout(isEditable() ? 3 : 2, false));
      widgetFactory.createLabel(existingContractComposite, "Contr&act");
      existingContractText = widgetFactory.createText(existingContractComposite, null);
      existingContractText.setEditable(isEditable());
      existingContractText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      existingContractText.addModifyListener(new ModifyListener() {
          @Override
          public void modifyText(ModifyEvent e) {
              updateLaunchConfigurationDialog();
          }
      });
      if (isEditable()) {
         browseContractButton = widgetFactory.createButton(existingContractComposite, "Brow&se", SWT.PUSH);
         browseContractButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 browseContract();
             }
         });
      }
      
      preconditionComposite = widgetFactory.createPlainComposite(contractComposite, SWT.NONE);
      GridLayout preconditionCompositeLayout = new GridLayout(2, false);
      preconditionComposite.setLayout(preconditionCompositeLayout);
      Label preconditionLabel = widgetFactory.createLabel(preconditionComposite, "Prec&ondition");
      preconditionLabel.setLayoutData(new GridData(GridData.BEGINNING, GridData.BEGINNING, false, false));
      int preconditionViewerCompositeStyle = SWT.BORDER;
      if (isEditable()) {
         preconditionViewerCompositeStyle |= SWT.V_SCROLL | SWT.H_SCROLL;
      }
      preconditionViewer = new JavaSnippetSourceViewer(preconditionComposite, preconditionViewerCompositeStyle);
      preconditionViewer.setEditable(isEditable());
      preconditionViewer.addPropertyChangeListener(JavaSnippetSourceViewer.PROP_TEXT, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      if (isEditable() && preconditionViewer.getDecoractionImage() != null) {
         preconditionCompositeLayout.horizontalSpacing += preconditionViewer.getDecoractionImage().getImageData().width;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      preconditionViewer.dispose();
      super.dispose();
   }

   /**
    * Updates the enabled state of the range text fields.
    */
   protected void updateRangeTextEditableState() {
      boolean executeMethodRange = isExecuteMethodRange();
      startLineText.setEditable(executeMethodRange && isEditable());
      startColumnText.setEditable(executeMethodRange && isEditable());
      endLineText.setEditable(executeMethodRange && isEditable());
      endColumnText.setEditable(executeMethodRange && isEditable());
      // Update used contract if required
      if (executeMethodRange && !useGeneratedContractButton.getSelection()) {
         useGeneratedContractButton.setSelection(true);
         useExistingContractButton.setSelection(false);
         updateShownContractComposite();
      }
      useExistingContractButton.setEnabled(!executeMethodRange && isEditable());
   }

   /**
    * Updates the shown contract.
    */
   protected void updateShownContractComposite() {
       // Update shown top control of stack layout
       boolean useExistingContract = useExistingContractButton.getSelection();
       if (useExistingContract) {
           contractCompositeLayout.topControl = existingContractComposite;
       }
       else {
           contractCompositeLayout.topControl = preconditionComposite;
       }
       // Layout ui
       contractComposite.layout();
   }

   /**
    * Updates the shown controls to start a new debug session or
    * to continue an existing one saved as *.proof file.
    */
   protected void updateShownSessionComposite() {
      // Update shown top control of stack layout
      boolean newDebugSession = newDebugSessionButton.getSelection();
      if (newDebugSession) {
          newOrContinueCompositeLayout.topControl = newDebugSessionComposite;
      }
      else {
         newOrContinueCompositeLayout.topControl = continueDebugSessionComposite;
      }
      // Layout ui
      newOrContinueComposite.layout();
   }

   /**
    * Unsets the loaded {@link InitConfig}.
    */
   protected void unsetInitConfig() {
       if (!ObjectUtil.equals(initConfigProject, projectText.getText())) {
           initConfig = null;
           initConfigProject = null;
       }
   }

   /**
    * Opens a dialog to select a contract for the specified method.
    */
   public void browseContract() {
       try {
           final IMethod method = getMethod();
           if (method != null && method.exists()) {
               IProject project = method.getResource().getProject();
               // Get source paths from class path
               final File location = KeYUtil.getSourceLocation(project);
               final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
               final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
               // Load location
               if (initConfig == null) {
                   IRunnableWithProgressAndResult<InitConfig> run = new AbstractRunnableWithProgressAndResult<InitConfig>() {
                       @Override
                       public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
                           KeYEnvironment<?> environment = null;
                           try {
                              SWTUtil.checkCanceled(monitor);
                              monitor.beginTask("Receiving contracts.", IProgressMonitor.UNKNOWN);
                              SWTUtil.checkCanceled(monitor);
                              environment = KeYEnvironment.load(location, classPaths, bootClassPath);
                              SWTUtil.checkCanceled(monitor);
                              setResult(environment.getInitConfig());
                              monitor.done();
                           }
                           catch (OperationCanceledException e) {
                              throw e;
                           }
                           catch (Exception e) {
                              throw new InvocationTargetException(e, e.getMessage());
                           }
                           finally {
                              if (environment != null) {
                                 environment.dispose();
                              }
                           }
                       }
                   };
                   getLaunchConfigurationDialog().run(true, false, run);
                   initConfig = run.getResult();
                   initConfigProject = project.getName();
               }
               if (initConfig != null) {
                   // Get method to proof in KeY
                   IProgramMethod pm = KeYUtil.getProgramMethod(method, initConfig.getServices().getJavaInfo());
                   if (pm != null) {
                       KeYJavaType type = pm.getContainerType();
                       ImmutableSet<FunctionalOperationContract> operationContracts = initConfig.getServices().getSpecificationRepository().getOperationContracts(type, pm);
                       // Open selection dialog
                       Services services = initConfig.getServices();
                       ContractSelectionDialog dialog = new ContractSelectionDialog(getShell(), ImmutableCollectionContentProvider.getInstance(), services);
                       dialog.setTitle("Contract selection");
                       dialog.setMessage("Select a contract to debug.");
                       dialog.setInput(operationContracts);
                       FunctionalOperationContract selectedContract = KeySEDUtil.findContract(operationContracts, getContractId());
                       if (selectedContract != null) {
                           dialog.setInitialSelections(new Object[] {selectedContract});
                       }
                       if (dialog.open() == ContractSelectionDialog.OK) {
                           Object result = dialog.getFirstResult();
                           if (result instanceof FunctionalOperationContract) {
                               FunctionalOperationContract foc = (FunctionalOperationContract)result;
                               existingContractText.setText(foc.getName());
                           }
                       }
                   }
                   else {
                       throw new IllegalStateException("Can't find method \"" + JDTUtil.getQualifiedMethodLabel(method) + "\" in KeY.");
                   }
               }
           }
       }
       catch (Exception e) {
           LogUtil.getLogger().logError(e);
           LogUtil.getLogger().openErrorDialog(getShell(), e);
       }
   }

   /**
    * Opens a dialog to select a *.proof file.
    */
   public void browseProofFile() {
      IFile selectedFile = getProofFile();
      IFile[] files = WorkbenchUtil.openFileSelection(getShell(), 
                                                      "File Selection", 
                                                      "Select a *." + KeYUtil.PROOF_FILE_EXTENSION + " file.", 
                                                      false, 
                                                      selectedFile != null && selectedFile.exists() ? new Object[] {selectedFile} : null, 
                                                      Collections.singleton(new FileExtensionViewerFilter(true, new String[] {KeYUtil.PROOF_FILE_EXTENSION})));
      if (files != null && files.length == 1) {
         proofFileText.setText(files[0].getFullPath().toString());
      }
   }
   
   /**
    * Returns the selected proof file.
    * @return The selected proof file.
    */
   protected IFile getProofFile() {
      try {
         String selectedText = proofFileText.getText();
         IFile selectedFile = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(selectedText));
         if (selectedFile != null && selectedFile.exists()) {
            return selectedFile;
         }
         else {
            return null;
         }
      }
      catch (Exception e) {
         return null;
      }
   }

   /**
    * <p>
    * Opens the dialog to select a Java project.
    * </p>
    * <p>
    * The implementation is oriented at {@link AbstractJavaMainTab#handleProjectButtonSelected()}
    * and {@link AbstractJavaMainTab#chooseJavaProject()}.
    * </p>
    */
   public void browseProject() {
       ILabelProvider labelProvider = new JavaElementLabelProvider(JavaElementLabelProvider.SHOW_DEFAULT);
       ElementListSelectionDialog dialog = new ElementListSelectionDialog(getShell(), labelProvider);
       dialog.setTitle("Project Selection"); 
       dialog.setMessage("Select a project to constrain your search."); 
       try {
           dialog.setElements(JDTUtil.getAllJavaProjects());
       }
       catch (JavaModelException jme) {
           LogUtil.getLogger().logError(jme);
       }
       IJavaProject javaProject = getJavaProject();
       if (javaProject != null) {
           dialog.setInitialSelections(new Object[] {javaProject});
       }
       if (dialog.open() == ElementListSelectionDialog.OK) {
           IJavaProject project = (IJavaProject)dialog.getFirstResult();
           projectText.setText(project.getElementName());
       }               
   }
   
   /**
    * Returns the selected {@link IJavaProject} or {@code null} if no one is defined.
    * @return The selected {@link IJavaProject} or {@code null} if no one is defined.
    */
   protected IJavaProject getJavaProject() {
       String projectName = projectText.getText().trim();
       return JDTUtil.getJavaProject(projectName);
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
           // Search all Java types
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
           IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(elements, IJavaSearchScope.SOURCES);
           AllTypesSearchEngine engine = new AllTypesSearchEngine();
           IType[] types = engine.searchTypes(getLaunchConfigurationDialog(), searchScope);
           // Open selection dialog
           DebugTypeSelectionDialog mmsd = new DebugTypeSelectionDialog(getShell(), types, "Select Type");
           IType selectedType = getType();
           if (selectedType != null) {
               mmsd.setInitialElementSelections(Collections.singletonList(selectedType));
           }
           if (mmsd.open() == DebugTypeSelectionDialog.OK) {
               Object[] results = mmsd.getResult();    
               if (results != null && results.length >= 1 && results[0] instanceof IType) {
                   IType type = (IType)results[0];
                   projectText.setText(type.getJavaProject().getElementName());
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
                   return null;
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
   
   /**
    * Returns the ID of the existing contract.
    * @return The ID of the existing contract.
    */
   protected String getContractId() {
       return existingContractText.getText();
   }

   /**
    * Opens a dialog to select a Java method ({@link IMethod}).
    */
   public void browseMethod() {
       try {
           // Search all Java types
           IType selectedType = getType();
           IJavaElement[] elements;
           if (selectedType != null && selectedType.exists()) {
               elements = new IJavaElement[] {selectedType};
           }
           else {
               elements = JDTUtil.getAllJavaProjects();
           }
           if (elements == null) {
               elements = new IJavaElement[] {};
           }
           IJavaSearchScope searchScope = SearchEngine.createJavaSearchScope(elements, IJavaSearchScope.SOURCES);
           AllOperationsSearchEngine engine = new AllOperationsSearchEngine();
           IMethod[] methods = engine.searchOperations(getLaunchConfigurationDialog(), searchScope);
           // Open selection dialog
           ILabelProvider labelProvider = new JavaElementLabelProvider(JavaElementLabelProvider.SHOW_DEFAULT);
           ElementListSelectionDialog dialog = new ElementListSelectionDialog(getShell(), labelProvider);
           dialog.setTitle("Method Selection"); 
           dialog.setMessage("Select a method to debug."); 
           dialog.setElements(methods);
           IMethod oldMethod = getMethod();
           if (oldMethod != null) {
               dialog.setInitialSelections(new Object[] {oldMethod});
           }
           if (dialog.open() == ElementListSelectionDialog.OK) {
               IMethod newMethod = (IMethod)dialog.getFirstResult();
               projectText.setText(KeySEDUtil.getProjectValue(newMethod));
               typeText.setText(KeySEDUtil.getTypeValue(newMethod));
               methodText.setText(KeySEDUtil.getMethodValue(newMethod));
           }
       }
       catch (Exception e) {
           LogUtil.getLogger().logError(e);
           LogUtil.getLogger().openErrorDialog(getShell(), e);
       }
   }

   /**
    * Returns the selected Java method ({@link IMethod}) or {@code null}
    * if no one is selected.
    * @return The selected Java method or {@code null} if no one is selected.
    */
   protected IMethod getMethod() {
       try {
           String text = methodText.getText().trim();
           if (!text.isEmpty()) {
               IType type = getType();
               if (type != null) {
                   return JDTUtil.getElementForQualifiedMethodLabel(type.getMethods(), text);
               }
               else {
                   return null;
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

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNotValidMessage() {
      String message = null;
      if (newDebugSessionButton.getSelection()) {
         // Validate Java project
         if (message == null) {
             IJavaProject project = getJavaProject();
             if (project == null || !project.exists()) {
                 message = "No existing Java project selected.";
             }
         }
         // Validate type
         if (message == null) {
             IType type = getType();
             if (type == null || !type.exists()) {
                 message = "No existing type selected.";
             }
         }
         // Validate method
         IMethod method = null;
         if (message == null) {
             method = getMethod();
             if (method == null || !method.exists()) {
                 message = "No existing method selected.";
             }
         }
         // Validate method range
         if (message == null && isExecuteMethodRange()) {
            // Make sure that line and columns of method range are valid integers
            int startLine = 0;
            try {
               startLine = getMethodRangeStartLine();
            }
            catch (NumberFormatException e) {
               message = "Start line of method range \"" + startLineText.getText() + "\" is no valid integer.";
            }
            int startColumn = 0;
            if (message == null) {
               try {
                  startColumn = getMethodRangeStartColumn();
               }
               catch (NumberFormatException e) {
                  message = "Start column of method range \"" + startColumnText.getText() + "\" is no valid integer.";
               }
            }
            int endLine = 0;
            if (message == null) {
               try {
                  endLine = getMethodRangeEndLine();
               }
               catch (NumberFormatException e) {
                  message = "To line of method range \"" + endLineText.getText() + "\" is no valid integer.";
               }
            }
            int endColumn = 0;
            if (message == null) {
               try {
                  endColumn = getMethodRangeEndColumn();
               }
               catch (NumberFormatException e) {
                  message = "To column of method range \"" + endColumnText.getText() + "\" is no valid integer.";
               }
            }
            // Make sure that defined start and end are in method's source range
            if (message == null) {
               try {
                  ISourceRange methodSourceRange = method.getSourceRange();
                  Position methodStartPosition = KeYUtil.getCursorPositionForOffset(method, methodSourceRange.getOffset());
                  Position methodEndPosition = KeYUtil.getCursorPositionForOffset(method, methodSourceRange.getOffset() + methodSourceRange.getLength());
                  Position startPosition = new KeYUtil.CursorPosition(startLine, startColumn);
                  if (startPosition.compareTo(methodStartPosition) < 0) {
                     message = "From method range (" + startPosition + ") must be greater or equal to \"" + methodStartPosition + "\".";
                  }
                  if (message == null && startPosition.compareTo(methodEndPosition) > 0) {
                     message = "From method range (" + startPosition + ") must be lower or equal to \"" + methodEndPosition + "\".";
                  }
                  Position endPosition = new KeYUtil.CursorPosition(endLine, endColumn);
                  if (message == null && endPosition.compareTo(methodEndPosition) > 0) {
                     message = "To method range (" + endPosition + ") must be lower or equal to \"" + methodEndPosition + "\".";
                  }
                  if (message == null && endPosition.compareTo(methodStartPosition) < 0) {
                     message = "To method range (" + endPosition + ") must be greater or equal to \"" + methodStartPosition + "\".";
                  }
                  // Make sure that end is after start
                  if (message == null && startPosition.compareTo(endPosition) > 0) {
                     message = "Method range to (" + startPosition + ") must be greater or equal to method range from (" + endPosition + ").";
                  }
               }
               catch (Exception e) {
                  message = e.getMessage();
               }
            }
         }
         // Validate contract
         if (message == null) {
             if (useExistingContractButton.getSelection()) {
                 if (StringUtil.isTrimmedEmpty(getContractId())) {
                     message = "No existing contract defined.";
                 }
             }
         }
      }
      else {
         // Validate proof file
         String proofText = proofFileText.getText();
         if (StringUtil.isEmpty(proofText)) {
            message = "No proof file to continue defined.";
         }
         else {
            IFile proofFile = getProofFile();
            if (proofFile != null && proofFile.exists()) {
               if (!KeYUtil.PROOF_FILE_EXTENSION.equals(proofFile.getFileExtension())) {
                  message = "Proof file \"" + proofFile.getFullPath().toString() + "\" has not the expected file extension \"" + KeYUtil.PROOF_FILE_EXTENSION + "\".";
               }
            }
            else {
               message = "Proof file \"" + proofText + "\" don't exist.";
            }
         }
      }
      return message;
   }

   /**
    * Checks if a method range should be used.
    * @return {@code true} use method range, {@code false} use complete method body.
    */
   protected boolean isExecuteMethodRange() {
      return executeMethodRangeButton.getSelection();
   }
   
   /**
    * Returns the start line of the method range.
    * @return The start line of the method range.
    * @throws NumberFormatException Occurred Exception
    */
   protected int getMethodRangeStartLine() throws NumberFormatException {
      return Integer.parseInt(startLineText.getText());
   }
   
   /**
    * Returns the start column of the method range.
    * @return The start column of the method range.
    * @throws NumberFormatException Occurred Exception
    */
   protected int getMethodRangeStartColumn() throws NumberFormatException {
      return Integer.parseInt(startColumnText.getText());
   }
   
   /**
    * Returns the end line of the method range.
    * @return The end line of the method range.
    * @throws NumberFormatException Occurred Exception
    */
   protected int getMethodRangeEndLine() throws NumberFormatException {
      return Integer.parseInt(endLineText.getText());
   }
   
   /**
    * Returns the end column of the method range.
    * @return The end column of the method range.
    * @throws NumberFormatException Occurred Exception
    */
   protected int getMethodRangeEndColumn() throws NumberFormatException {
      return Integer.parseInt(endColumnText.getText());
   }

   /**
    * Updates the precondition viewer composite by setting the
    * correct context for content assistant.
    */
   protected void updatePreconditionViewerComposite() {
      IJavaDebugContentAssistContext context = null;
      if (getType() == null) {
         context = new TypeContext(null, -1);
      }
      else {
         int position= -1;
         IMethod method = getMethod();
         if (method != null) {
            try {
               Block body = JDTUtil.getMethodBody(method);
               if (body != null) {
                  position = body.getStartPosition() + 1; // Go inside the method body directly after {
               }
               try {
                  if (isExecuteMethodRange()) {
                     int offset = KeYUtil.getOffsetForCursorPosition(method, 
                                                                     getMethodRangeStartLine(), 
                                                                     getMethodRangeStartColumn());
                     if (offset >= 0) {
                        position = offset;
                     }
                  }
               }
               catch (Exception e) {
                  // Nothing to do, use method body position
               }
            }
            catch (JavaModelException e) {
               LogUtil.getLogger().logError(e);
            }
         }
         context = new TypeContext(getType(), position);
      }
      preconditionViewer.setContentAssistContext(context);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeFrom(ILaunchConfiguration configuration) {
      try {
         boolean newDebugSession = KeySEDUtil.isNewDebugSession(configuration);
         newDebugSessionButton.setSelection(newDebugSession);
         continueDebugSessionButton.setSelection(!newDebugSession);
         SWTUtil.setText(proofFileText, KeySEDUtil.getFileToLoadValue(configuration));
         SWTUtil.setText(projectText, KeySEDUtil.getProjectValue(configuration));
         SWTUtil.setText(typeText, KeySEDUtil.getTypeValue(configuration));
         SWTUtil.setText(methodText, KeySEDUtil.getMethodValue(configuration));
         boolean useExistingContract = KeySEDUtil.isUseExistingContractValue(configuration);
         useGeneratedContractButton.setSelection(!useExistingContract);
         useExistingContractButton.setSelection(useExistingContract);
         SWTUtil.setText(existingContractText, KeySEDUtil.getExistingContractValue(configuration));
         preconditionViewer.setText(KeySEDUtil.getPrecondition(configuration));
         boolean executeMethodRange = KeySEDUtil.isExecuteMethodRange(configuration);
         executeMethodBodyButton.setSelection(!executeMethodRange);
         executeMethodRangeButton.setSelection(executeMethodRange);
         startLineText.setText(KeySEDUtil.getMethodRangeStartLine(configuration) + StringUtil.EMPTY_STRING);
         startColumnText.setText(KeySEDUtil.getMethodRangeStartColumn(configuration) + StringUtil.EMPTY_STRING);
         endLineText.setText(KeySEDUtil.getMethodRangeEndLine(configuration) + StringUtil.EMPTY_STRING);
         endColumnText.setText(KeySEDUtil.getMethodRangeEndColumn(configuration) + StringUtil.EMPTY_STRING);
         updateShownSessionComposite();
         updateRangeTextEditableState();
         updateShownContractComposite();
         updatePreconditionViewerComposite();
      } 
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * Shows the content of the given {@link KeYLaunchSettings}.
    * @param settings The {@link KeYLaunchSettings} to show.
    */
   public void initializeFrom(KeYLaunchSettings settings) {
      boolean newDebugSession = settings.isNewDebugSession();
      newDebugSessionButton.setSelection(newDebugSession);
      continueDebugSessionButton.setSelection(!newDebugSession);
      SWTUtil.setText(proofFileText, settings.getProofFileToContinue());
      IMethod method = settings.getMethod();
      SWTUtil.setText(projectText, KeySEDUtil.getProjectValue(method));
      SWTUtil.setText(typeText, KeySEDUtil.getTypeValue(method));
      SWTUtil.setText(methodText, settings.getMethodSignature());
      boolean useExistingContract = settings.isUseExistingContract();
      useGeneratedContractButton.setSelection(!useExistingContract);
      useExistingContractButton.setSelection(useExistingContract);
      SWTUtil.setText(existingContractText, settings.getExistingContract());
      preconditionViewer.setText(settings.getPrecondition());
      boolean executeMethodRange = settings.isExecuteMethodRange();
      executeMethodBodyButton.setSelection(!executeMethodRange);
      executeMethodRangeButton.setSelection(executeMethodRange);
      Position startPosition = settings.getMethodRangeStart();
      if (startPosition != null) {
         startLineText.setText(startPosition.getLine() + StringUtil.EMPTY_STRING);
         startColumnText.setText(startPosition.getColumn() + StringUtil.EMPTY_STRING);
      }
      Position endPosition = settings.getMethodRangeEnd();
      if (endPosition != null) {
         endLineText.setText(endPosition.getLine() + StringUtil.EMPTY_STRING);
         endColumnText.setText(endPosition.getColumn() + StringUtil.EMPTY_STRING);
      }
      updateShownSessionComposite();
      updateRangeTextEditableState();
      updateShownContractComposite();
      updatePreconditionViewerComposite();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void performApply(ILaunchConfigurationWorkingCopy configuration) {
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_NEW_DEBUG_SESSION, newDebugSessionButton.getSelection());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD, proofFileText.getText());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, projectText.getText());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, typeText.getText());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, methodText.getText());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_EXISTING_CONTRACT, useExistingContractButton.getSelection());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXISTING_CONTRACT, existingContractText.getText());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PRECONDITION, preconditionViewer.getText());
      configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXECUTE_METHOD_RANGE, isExecuteMethodRange());
      try {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_LINE, getMethodRangeStartLine());
      }
      catch (NumberFormatException e) {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_LINE, StringUtil.EMPTY_STRING);
      }
      try {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_COLUMN, getMethodRangeStartColumn());
      }
      catch (NumberFormatException e) {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_COLUMN, StringUtil.EMPTY_STRING);
      }
      try {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_LINE, getMethodRangeEndLine());
      }
      catch (NumberFormatException e) {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_LINE, StringUtil.EMPTY_STRING);
      }
      try {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_COLUMN, getMethodRangeEndColumn());
      }
      catch (NumberFormatException e) {
         configuration.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_COLUMN, StringUtil.EMPTY_STRING);
      }
   }
}