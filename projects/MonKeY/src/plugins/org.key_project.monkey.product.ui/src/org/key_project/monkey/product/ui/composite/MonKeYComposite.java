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

package org.key_project.monkey.product.ui.composite;

import java.io.File;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.PlatformUI;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.monkey.product.ui.model.MonKeYProof;
import org.key_project.monkey.product.ui.model.MonKeYProofResult;
import org.key_project.monkey.product.ui.provider.MonKeYProofLabelProvider;
import org.key_project.monkey.product.ui.util.LogUtil;
import org.key_project.monkey.product.ui.util.MonKeYUtil;
import org.key_project.monkey.product.ui.util.MonKeYUtil.MonKeYProofSums;
import org.key_project.monkey.product.ui.view.MonKeYView;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

/**
 * Content in the {@link MonKeYView} that contains the whole
 * program logic.
 * @author Martin Hentschel
 */
public class MonKeYComposite extends Composite {
    /**
     * Key to store the location in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_LOCATION = "location";
    
    /**
     * Key to store the boot class path in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_BOOT_CLASS_PATH = "bootClassPath";

    /**
     * Key to store the show main window flag in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_SHOW_WINDOW = "showKeYMainWindow";

    /**
     * Key to store the method treatment option in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_EXPAND_METHODS = "expandMethods";

    /**
     * Key to store the use dependency contracts option in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_USE_DEPENDENCY_CONTRACTS = "useDependencyContracts";

    /**
     * Key to store the use query treatment option in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_USE_QUERY = "useQuery";

    /**
     * Key to store the use arithmetic treatment option in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_USE_DEF_OPS = "useDefOps";

    /**
     * Key to store the proof directory value in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_PROOF_DIRECTORY = "proofDirectory";
    
    /**
     * Defines the location.
     */
    private Text locationText;
    
    /**
     * Defines the boot class path.
     */
    private Text bootClassPathText;
    
    /**
     * Defines if the main window should be shown or not.
     */
    private Button showKeYWindowButton;
    
    /**
     * Shows all available proofs.
     */
    private TableViewer proofViewer;
    
    /**
     * Contains all proofs shown in {@link #proofViewer}.
     */
    private List<MonKeYProof> proofs;
    
    /**
     * The used {@link MonKeYProofLabelProvider} in {@link #proofViewer}.
     */
    private MonKeYProofLabelProvider labelProvider;
    
    /**
     * Listens for changes on {@link #labelProvider}.
     */
    private ILabelProviderListener labelProviderListener = new ILabelProviderListener() {
       @Override
       public void labelProviderChanged(LabelProviderChangedEvent event) {
          handleLabelProviderChanged(event);
       }
    };
    
    /**
     * {@link TableViewerColumn} of {@link #proofViewer} which shows the proof reuse status.
     */
    private TableViewerColumn proofReuseColumn;
    
    /**
     * {@link TableViewerColumn} of {@link #proofViewer} which shows the proof result.
     */
    private TableViewerColumn proofResultColumn;
    
    /**
     * {@link TableViewerColumn} of {@link #proofViewer} which shows the nodes.
     */
    private TableViewerColumn proofNodesColumn;

    /**
     * {@link TableViewerColumn} of {@link #proofViewer} which shows the branches.
     */
    private TableViewerColumn proofBranchesColumn;

    /**
     * {@link TableViewerColumn} of {@link #proofViewer} which shows the time.
     */
    private TableViewerColumn proofTimeColumn;
    
    /**
     * Defines the proof search strategy option "Method Treatment" with option "Contract".
     */
    private Button methodTreatmentContractButton;
    
    /**
     * Defines the proof search strategy option "Method Treatment" with option "Expand".
     */
    private Button methodTreatmentExpandButton;
    
    /**
     * Defines the proof search strategy option "Dependency contracts" with option "On".
     */
    private Button dependencyContractsOnButton;
    
    /**
     * Defines the proof search strategy option "Dependency contracts" with option "Off".
     */
    private Button dependencyContractsOffButton;
    
    /**
     * Defines the proof search strategy option "Query treatment" with option "On".
     */
    private Button queryTreatmentOnButton;
    
    /**
     * Defines the proof search strategy option "Query treatment" with option "Off".
     */
    private Button queryTreatmentOffButton;
    
    /**
     * Defines the proof search strategy option "Arithmetic treatment" with option "Base".
     */
    private Button arithmeticTreatmentBaseButton;
    
    /**
     * Defines the proof search strategy option "Arithmetic treatment" with option "DefOps".
     */
    private Button arithmeticTreatmentDefOpsButton;
    
    /**
     * Label for {@link #loadTimeText}.
     */
    private Label loadLabel;
    
    /**
     * Shows the time which was needed to load the source code in KeY.
     */
    private Text loadTimeText;
    
    /**
     * The time shown in {@link #loadTimeText}.
     */
    private long loadingTime;
    
    /**
     * Shows accumulated values.
     */
    private Text sumText;
    
    /**
     * The path to a directory which provides *.proof files or to save such files in.
     */
    private String proofDirectory;
    
    /**
     * Constructor.
     * @param parent The parent {@link Composite}.
     * @param style The style to use.
     */
    public MonKeYComposite(Composite parent, int style) {
        super(parent, style);
        setLayout(new GridLayout(1, false));
        // Source group
        Group sourceGroup = new Group(this, SWT.NONE);
        sourceGroup.setText("Source");
        sourceGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        sourceGroup.setLayout(new GridLayout(1, false));
        // Location
        Composite locationComposite = new Composite(sourceGroup, SWT.NONE);
        locationComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        locationComposite.setLayout(new GridLayout(2, false));
        Label locationLabel = new Label(locationComposite, SWT.NONE);
        locationLabel.setText("&Location");
        locationText = new Text(locationComposite, SWT.BORDER);
        locationText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        Label bootClassPathLabel = new Label(locationComposite, SWT.NONE);
        bootClassPathLabel.setText("&Boot Class Path");
        bootClassPathText = new Text(locationComposite, SWT.BORDER);
        bootClassPathText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        Composite loadComposite = new Composite(sourceGroup, SWT.NONE);
        loadComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        loadComposite.setLayout(new GridLayout(4, false)); 
        showKeYWindowButton = new Button(loadComposite, SWT.CHECK);
        showKeYWindowButton.setText("Sho&w KeY main window");
        showKeYWindowButton.setSelection(true);
        Button loadSourceButton = new Button(loadComposite, SWT.PUSH);
        loadSourceButton.setText("Loa&d");
        loadSourceButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        loadSourceButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                loadSource();
            }
        });
        loadLabel = new Label(loadComposite, SWT.NONE);
        loadLabel.setText("Load &Time (milliseconds)");
        loadTimeText = new Text(loadComposite, SWT.BORDER);
        loadTimeText.setEditable(false);
        // Proof group
        Group proofGroup = new Group(this, SWT.NONE);
        proofGroup.setText("Proofs");
        proofGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
        proofGroup.setLayout(new GridLayout(1, false));
        // Proof search strategy
        Composite proofSearchStrategyOptionComposite = new Composite(proofGroup, SWT.NONE);
        proofSearchStrategyOptionComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        proofSearchStrategyOptionComposite.setLayout(new GridLayout(4, true));
        Group methodTreatmentGroup = new Group(proofSearchStrategyOptionComposite, SWT.NONE);
        methodTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        methodTreatmentGroup.setLayout(new GridLayout(2, false));
        methodTreatmentGroup.setText("Method Treatment");
        methodTreatmentContractButton = new Button(methodTreatmentGroup, SWT.RADIO);
        methodTreatmentContractButton.setText("&Contract");
        methodTreatmentExpandButton = new Button(methodTreatmentGroup, SWT.RADIO);
        methodTreatmentExpandButton.setSelection(true);
        methodTreatmentExpandButton.setText("E&xpand");
        Group dependencyContractsGroup = new Group(proofSearchStrategyOptionComposite, SWT.NONE);
        dependencyContractsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        dependencyContractsGroup.setLayout(new GridLayout(2, false));
        dependencyContractsGroup.setText("Dependency Contracts");
        dependencyContractsOnButton = new Button(dependencyContractsGroup, SWT.RADIO);
        dependencyContractsOnButton.setText("O&n");
        dependencyContractsOnButton.setSelection(true);
        dependencyContractsOffButton = new Button(dependencyContractsGroup, SWT.RADIO);
        dependencyContractsOffButton.setText("O&ff");
        Group queryTreatmentGroup = new Group(proofSearchStrategyOptionComposite, SWT.NONE);
        queryTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        queryTreatmentGroup.setLayout(new GridLayout(2, false));
        queryTreatmentGroup.setText("Query Treatment");
        queryTreatmentOnButton = new Button(queryTreatmentGroup, SWT.RADIO);
        queryTreatmentOnButton.setText("On");
        queryTreatmentOnButton.setSelection(true);
        queryTreatmentOffButton = new Button(queryTreatmentGroup, SWT.RADIO);
        queryTreatmentOffButton.setText("Off");
        Group arithmeticTreatmentGroup = new Group(proofSearchStrategyOptionComposite, SWT.NONE);
        arithmeticTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        arithmeticTreatmentGroup.setLayout(new GridLayout(2, false));
        arithmeticTreatmentGroup.setText("Arithmetic Treatment");
        arithmeticTreatmentBaseButton = new Button(arithmeticTreatmentGroup, SWT.RADIO);
        arithmeticTreatmentBaseButton.setText("&Base");
        arithmeticTreatmentDefOpsButton = new Button(arithmeticTreatmentGroup, SWT.RADIO);
        arithmeticTreatmentDefOpsButton.setText("DefO&ps");
        arithmeticTreatmentDefOpsButton.setSelection(true);
        // Proof viewer
        Composite proofViewerComposite = new Composite(proofGroup, SWT.NONE);
        proofViewerComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
        TableColumnLayout proofViewerLayout = new TableColumnLayout();
        proofViewerComposite.setLayout(proofViewerLayout);
        proofViewer = new TableViewer(proofViewerComposite, SWT.MULTI | SWT.FULL_SELECTION);
        proofViewer.getTable().setHeaderVisible(true);
        TableViewerColumn typeColumn = new TableViewerColumn(proofViewer, style);
        typeColumn.getColumn().setText("Type");
        typeColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(typeColumn.getColumn(), new ColumnWeightData(15));
        TableViewerColumn targetColumn = new TableViewerColumn(proofViewer, style);
        targetColumn.getColumn().setText("Target");
        targetColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(targetColumn.getColumn(), new ColumnWeightData(15));
        TableViewerColumn contractColumn = new TableViewerColumn(proofViewer, style);
        contractColumn.getColumn().setText("Contract");
        contractColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(contractColumn.getColumn(), new ColumnWeightData(35));
        proofReuseColumn = new TableViewerColumn(proofViewer, style);
        proofReuseColumn.getColumn().setText("Proof Reuse");
        proofReuseColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofReuseColumn.getColumn(), new ColumnWeightData(15));
        proofResultColumn = new TableViewerColumn(proofViewer, style);
        proofResultColumn.getColumn().setText("Proof Result");
        proofResultColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofResultColumn.getColumn(), new ColumnWeightData(15));
        proofNodesColumn = new TableViewerColumn(proofViewer, style);
        proofNodesColumn.getColumn().setText("Nodes");
        proofNodesColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofNodesColumn.getColumn(), new ColumnWeightData(5));
        proofBranchesColumn = new TableViewerColumn(proofViewer, style);
        proofBranchesColumn.getColumn().setText("Branches");
        proofBranchesColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofBranchesColumn.getColumn(), new ColumnWeightData(5));
        proofTimeColumn = new TableViewerColumn(proofViewer, style);
        proofTimeColumn.getColumn().setText("Time (milliseconds)");
        proofTimeColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofTimeColumn.getColumn(), new ColumnWeightData(5));
        
        SWTUtil.makeTableColumnsSortable(proofViewer);
        proofViewer.setContentProvider(ArrayContentProvider.getInstance());
        labelProvider = new MonKeYProofLabelProvider();
        labelProvider.addListener(labelProviderListener);
        proofViewer.setLabelProvider(labelProvider);
        // Accumulated values
        Composite sumComposite = new Composite(proofGroup, SWT.NONE);
        sumComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        sumComposite.setLayout(new GridLayout(2, false));
        Label sumLabel = new Label(sumComposite, SWT.NONE);
        sumLabel.setText("S&um");
        sumText = new Text(sumComposite, SWT.BORDER);
        sumText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        sumText.setEditable(false);
        // Buttons
        Composite buttonComposite = new Composite(proofGroup, SWT.NONE);
        buttonComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        buttonComposite.setLayout(new GridLayout(6, false));
        Button openKeYButton = new Button(buttonComposite, SWT.PUSH);
        openKeYButton.setText("&Open KeY");
        openKeYButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                openKeY();
            }
        });
        Button loadProofsButton = new Button(buttonComposite, SWT.PUSH);
        loadProofsButton.setText("L&oad selected Proofs");
        loadProofsButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                loadProofs();
            }
        });
        Button startProofsButton = new Button(buttonComposite, SWT.PUSH);
        startProofsButton.setText("&Start selected proofs");
        startProofsButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        startProofsButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                startProofs();
            }
        });
        Button saveProofsButton = new Button(buttonComposite, SWT.PUSH);
        saveProofsButton.setText("Sa&ve selected Proofs");
        saveProofsButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                saveProofs();
            }
        });
        Button exportButton = new Button(buttonComposite, SWT.PUSH);
        exportButton.setText("&Export Proofs");
        exportButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                exportProofs();
            }
        });
        Button helpButton = new Button(buttonComposite, SWT.PUSH);
        helpButton.setText("&Help");
        helpButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                PlatformUI.getWorkbench().getHelpSystem().displayHelpResource("/org.key_project.monkey.help/help/tutorial/Tutorial.htm");
            }
        });
    }

   /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
       labelProvider.removeListener(labelProviderListener);
       labelProvider.dispose();
       super.dispose();
    }

    /**
     * When the label provider has changed.
     * @param event The event.
     */
    protected void handleLabelProviderChanged(LabelProviderChangedEvent event) {
       updateSumText();
    }

    /**
     * Updates the shown value in the sum text.
     */
    protected void updateSumText() {
       // Compute sums
       MonKeYProofSums sums = MonKeYUtil.computeSums(proofs);
       // Compute sum text to show
       StringBuffer sb = new StringBuffer();
       sb.append(proofResultColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(sums.getClosedCount());
       sb.append(" / ");
       sb.append(proofs.size());
       sb.append(" ");
       sb.append(MonKeYProofResult.CLOSED.getDisplayText());
       sb.append(", ");
       sb.append(proofNodesColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(sums.getNodes());
       sb.append(", ");
       sb.append(proofBranchesColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(sums.getBranches());
       sb.append(", ");
       sb.append(proofTimeColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(sums.getTime());
       sb.append(", ");
       sb.append(proofTimeColumn.getColumn().getText());
       sb.append(" + ");
       sb.append(loadLabel.getText());
       sb.append(" = ");
       sb.append(loadingTime + sums.getTime());
       // Show sum text
       sumText.setText(sb.toString());
    }
    
    /**
     * Opens the main window of KeY.
     */
    public void openKeY() {
        try {
            KeYUtil.openMainWindowAsync();
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getShell(), e);
        }
    }

   /**
     * Enables or disables the controls with proof specific options.
     * @param enabled {@code true} set enabled state, {@code false} set disabled state.
     */
    protected void setProofSearchStrategyOptionsEnabled(boolean enabled) {
       if (!isDisposed()) {
          methodTreatmentContractButton.setEnabled(enabled);
          methodTreatmentExpandButton.setEnabled(enabled);
          dependencyContractsOnButton.setEnabled(enabled);
          dependencyContractsOffButton.setEnabled(enabled);
          queryTreatmentOnButton.setEnabled(enabled);
          queryTreatmentOffButton.setEnabled(enabled);
          arithmeticTreatmentBaseButton.setEnabled(enabled);
          arithmeticTreatmentDefOpsButton.setEnabled(enabled);
       }
    }

    /**
     * Starts all available proofs.
     */
    public void startProofs() {
        if (proofViewer.getInput() instanceof List<?>) {
            setProofSearchStrategyOptionsEnabled(false);
            // Get selected proofs
            final List<?> selectedProofs = SWTUtil.toList(proofViewer.getSelection());
            // Get strategy properties
            final boolean expandMethods = methodTreatmentExpandButton.getSelection();
            final boolean useDependencyContracts = dependencyContractsOnButton.getSelection();
            final boolean useQuery = queryTreatmentOnButton.getSelection();
            final boolean useDefOps = arithmeticTreatmentDefOpsButton.getSelection();
            new AbstractKeYMainWindowJob("Proving") {
                @Override
                protected IStatus run(IProgressMonitor monitor) {
                    try {
                        SWTUtil.checkCanceled(monitor);
                        monitor.beginTask("Proving", selectedProofs.size());
                        for (Object obj : selectedProofs) {
                            SWTUtil.checkCanceled(monitor);
                            if (obj instanceof MonKeYProof) {
                                ((MonKeYProof)obj).startProof(expandMethods, useDependencyContracts, useQuery, useDefOps);
                            }
                            monitor.worked(1);
                        }
                        return Status.OK_STATUS;
                    }
                    catch (OperationCanceledException e) {
                        return Status.CANCEL_STATUS;
                    }
                    catch (Exception e) {
                        return LogUtil.getLogger().createErrorStatus(e);
                    }
                    finally {
                        monitor.done();
                        if (!isDisposed()) {
                           getDisplay().syncExec(new Runnable() {
                              @Override
                              public void run() {
                                 setProofSearchStrategyOptionsEnabled(true);
                              }
                           });
                        }
                    }
                }
            }.schedule();
        }
    }

   /**
    * Saves all proofs in a user defined directory.
    */
   public void saveProofs() {
      try {
          // Get selected proofs
          final List<?> selectedProofs = SWTUtil.toList(proofViewer.getSelection());
          // Select directory
          DirectoryDialog dialog = new DirectoryDialog(getShell());
          dialog.setFilterPath(proofDirectory);
          dialog.setText("Save proofs");
          dialog.setMessage("Select a directory to save proofs in.\nIt is recommended to select an empty directory.");
          String selectedPath = dialog.open();
          if (selectedPath != null) {
             proofDirectory = selectedPath;
             if (proofs != null) {
                // Check for existing files
                List<String> existingFiles = new LinkedList<String>();
                for (Object obj : selectedProofs) {
                    if (obj instanceof MonKeYProof) {
                        MonKeYProof proof = (MonKeYProof)obj;
                        if (proof.hasProofInKeY() && proof.existsProofFile(proofDirectory)) {
                            existingFiles.add(proof.getProofFileName());
                        }
                    }
                }
                boolean goOn = true;
                if (!existingFiles.isEmpty()) {
                   goOn = MessageDialog.openQuestion(getShell(), "Replace existing files?", "Replace the following existing files?\n" + CollectionUtil.toString(existingFiles, ",\n"));
                }
                if (goOn) {
                   // Save proofs
                   new AbstractKeYMainWindowJob("Saving proofs") {
                      @Override
                      protected IStatus run(IProgressMonitor monitor) {
                          try {
                              SWTUtil.checkCanceled(monitor);
                              monitor.beginTask("Saving proofs", selectedProofs.size());
                              for (Object obj : selectedProofs) {
                                  if (obj instanceof MonKeYProof) {
                                      ((MonKeYProof)obj).save(proofDirectory);
                                  }
                                  monitor.worked(1);
                              }
                              return Status.OK_STATUS;
                          }
                          catch (OperationCanceledException e) {
                              return Status.CANCEL_STATUS;
                          }
                          catch (Exception e) {
                              return LogUtil.getLogger().createErrorStatus(e);
                          }
                          finally {
                              monitor.done();
                          }
                      }
                  }.schedule();
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
    * Loads available proofs.
    */
   public void loadProofs() {
      try {
          // Get selected proofs
          final List<?> selectedProofs = SWTUtil.toList(proofViewer.getSelection());
          // Select directory
          DirectoryDialog dialog = new DirectoryDialog(getShell());
          dialog.setFilterPath(proofDirectory);
          dialog.setText("Load proofs");
          dialog.setMessage("Select a directory to load proofs from.");
          String selectedPath = dialog.open();
          if (selectedPath != null) {
             proofDirectory = selectedPath;
             if (proofs != null) {
                final String bootClassPath = bootClassPathText.getText();
                new AbstractKeYMainWindowJob("Loading proofs") {
                   @Override
                   protected IStatus run(IProgressMonitor monitor) {
                       try {
                           SWTUtil.checkCanceled(monitor);
                           monitor.beginTask("Loading proofs", selectedProofs.size());
                           for (Object obj : selectedProofs) {
                               SWTUtil.checkCanceled(monitor);
                               if (obj instanceof MonKeYProof) {
                                   ((MonKeYProof)obj).loadProof(proofDirectory, bootClassPath);
                               }
                               monitor.worked(1);
                           }
                           return Status.OK_STATUS;
                       }
                       catch (OperationCanceledException e) {
                           return Status.CANCEL_STATUS;
                       }
                       catch (Exception e) {
                           return LogUtil.getLogger().createErrorStatus(e);
                       }
                       finally {
                           monitor.done();
                       }
                   }
               }.schedule();
             }
          }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
   }

    /**
     * Exports the proof table content into a CSV file.
     */
    public void exportProofs() {
        try {
            FileDialog dialog = new FileDialog(getShell(), SWT.SAVE);
            dialog.setFilterExtensions(new String[] {"*.*", "*.csv"});
            dialog.setFilterIndex(1);
            dialog.setText("Export to CSV");
            String filePath = dialog.open();
            if (filePath != null) {
                SWTUtil.csvExport(proofViewer.getTable(), new File(filePath));
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getShell(), e);
        }
    }

    /**
     * Loads the defined location in KeY.
     */
    public void loadSource() {
        try {
            // Load new source
            final File location = new File(locationText.getText());
            final File bootClassPath = !StringUtil.isTrimmedEmpty(bootClassPathText.getText()) ? new File(bootClassPathText.getText()) : null;
            final boolean showKeYMainWindow = showKeYWindowButton.getSelection();
            if (location.exists()) {
                new AbstractKeYMainWindowJob("Loading in KeY") {
                    @Override
                    protected IStatus run(IProgressMonitor monitor) {
                        final long loadStartTime = System.currentTimeMillis();
                        try {
                            SWTUtil.checkCanceled(monitor);
                            // Remove old proofs
                            if (proofs != null) {
                               for (MonKeYProof proof : proofs) {
                                  proof.removeProof();
                               }
                            }
                            // Unload old source
                            getDisplay().syncExec(new Runnable() {
                               @Override
                               public void run() {
                                  proofs = null;
                                  loadingTime = 0l;
                                  proofViewer.setInput(Collections.EMPTY_LIST);
                                  loadTimeText.setText(StringUtil.EMPTY_STRING);
                                  sumText.setText(StringUtil.EMPTY_STRING);
                               }
                            });
                            // Open main window to avoid repaint problems.
                            if (showKeYMainWindow) {
                                KeYUtil.openMainWindow();
                            }
                            // Load 
                            proofs = MonKeYUtil.loadSourceInKeY(monitor, location, bootClassPath, showKeYMainWindow);
                            SWTUtil.checkCanceled(monitor);
                            if (!getDisplay().isDisposed()) {
                                getDisplay().syncExec(new Runnable() {
                                    @Override
                                    public void run() {
                                        if (!proofViewer.getTable().isDisposed()) {
                                            proofViewer.setInput(proofs);
                                        }
                                    }
                                });
                            }
                            // Select all proofs
                            getDisplay().syncExec(new Runnable() {
                               @Override
                               public void run() {
                                  proofViewer.getTable().selectAll();
                               }
                            });
                            return Status.OK_STATUS;
                        }
                        catch (OperationCanceledException e) {
                            return Status.CANCEL_STATUS;
                        }
                        catch (Exception e) {
                            return LogUtil.getLogger().createErrorStatus(e);
                        }
                        finally {
                            monitor.done();
                            loadingTime = System.currentTimeMillis() - loadStartTime;
                            if (!loadTimeText.isDisposed()) {
                               loadTimeText.getDisplay().syncExec(new Runnable() {
                                  @Override
                                  public void run() {
                                     loadTimeText.setText(loadingTime + "");
                                  }
                               });
                            }
                        }
                    }
                }.schedule();
            }
            else {
                throw new IllegalArgumentException("The location \"" + location + "\" is no existing file/directory.");
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getShell(), e);
        }
    }

   /**
     * Loads the previous state from the given {@link IMemento}.
     * @param memento The {@link IMemento} to load from.
     */
    public void loadState(IMemento memento) {
        if (memento != null) {
            SWTUtil.setText(locationText, memento.getString(MEMENTO_KEY_LOCATION)); 
            SWTUtil.setText(bootClassPathText, memento.getString(MEMENTO_KEY_BOOT_CLASS_PATH)); 
            Boolean showKeYWindow = memento.getBoolean(MEMENTO_KEY_SHOW_WINDOW);
            showKeYWindowButton.setSelection(showKeYWindow == null || showKeYWindow.booleanValue());
            Boolean expandMethods = memento.getBoolean(MEMENTO_KEY_EXPAND_METHODS);
            methodTreatmentContractButton.setSelection(expandMethods != null && !expandMethods.booleanValue());
            methodTreatmentExpandButton.setSelection(expandMethods == null || expandMethods.booleanValue());
            Boolean useDependencyContracts = memento.getBoolean(MEMENTO_KEY_USE_DEPENDENCY_CONTRACTS);
            dependencyContractsOnButton.setSelection(useDependencyContracts == null || useDependencyContracts.booleanValue());
            dependencyContractsOffButton.setSelection(useDependencyContracts != null && !useDependencyContracts.booleanValue());
            Boolean useQuery = memento.getBoolean(MEMENTO_KEY_USE_QUERY);
            queryTreatmentOnButton.setSelection(useQuery == null || useQuery.booleanValue());
            queryTreatmentOffButton.setSelection(useQuery != null && !useQuery.booleanValue());
            Boolean useDefOpy = memento.getBoolean(MEMENTO_KEY_USE_DEF_OPS);
            arithmeticTreatmentBaseButton.setSelection(useDefOpy != null && !useDefOpy.booleanValue());
            arithmeticTreatmentDefOpsButton.setSelection(useDefOpy == null || useDefOpy.booleanValue());
            proofDirectory = memento.getString(MEMENTO_KEY_PROOF_DIRECTORY);
        }
    }

    /**
     * Saves the current state into the given {@link IMemento}.
     * @param memento The {@link IMemento} to save state in.
     */
    public void saveState(IMemento memento) {
        if (memento != null) {
            memento.putString(MEMENTO_KEY_LOCATION, locationText.getText());
            memento.putString(MEMENTO_KEY_BOOT_CLASS_PATH, bootClassPathText.getText());
            memento.putBoolean(MEMENTO_KEY_SHOW_WINDOW, showKeYWindowButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_EXPAND_METHODS, methodTreatmentExpandButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_USE_DEPENDENCY_CONTRACTS, dependencyContractsOnButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_USE_QUERY, queryTreatmentOnButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_USE_DEF_OPS, arithmeticTreatmentDefOpsButton.getSelection());
            memento.putString(MEMENTO_KEY_PROOF_DIRECTORY, proofDirectory);
        }
    }
}