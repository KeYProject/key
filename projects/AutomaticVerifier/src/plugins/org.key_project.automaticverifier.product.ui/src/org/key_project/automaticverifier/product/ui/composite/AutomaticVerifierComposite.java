package org.key_project.automaticverifier.product.ui.composite;

import java.io.File;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
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
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IMemento;
import org.key_project.automaticverifier.product.ui.model.AutomaticProof;
import org.key_project.automaticverifier.product.ui.model.AutomaticProofResult;
import org.key_project.automaticverifier.product.ui.provider.AutomaticProofLabelProvider;
import org.key_project.automaticverifier.product.ui.util.LogUtil;
import org.key_project.automaticverifier.product.ui.view.AutomaticVerifierView;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Content in the {@link AutomaticVerifierView} that contains the whole
 * program logic.
 * @author Martin Hentschel
 */
public class AutomaticVerifierComposite extends Composite {
    /**
     * Key to store the location in an {@link IMemento}.
     */
    public static final String MEMENTO_KEY_LOCATION = "location";

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
     * Defines the location.
     */
    private Text locationText;
    
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
    private List<AutomaticProof> proofs;
    
    /**
     * The used {@link AutomaticProofLabelProvider} in {@link #proofViewer}.
     */
    private AutomaticProofLabelProvider labelProvider;
    
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
     * Constructor.
     * @param parent The parent {@link Composite}.
     * @param style The style to use.
     */
    public AutomaticVerifierComposite(Composite parent, int style) {
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
        Composite loadComposite = new Composite(sourceGroup, SWT.NONE);
        loadComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        loadComposite.setLayout(new GridLayout(4, false)); 
        showKeYWindowButton = new Button(loadComposite, SWT.CHECK);
        showKeYWindowButton.setText("Sho&w KeY main window");
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
        methodTreatmentExpandButton.setText("E&xpand");
        Group dependencyContractsGroup = new Group(proofSearchStrategyOptionComposite, SWT.NONE);
        dependencyContractsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        dependencyContractsGroup.setLayout(new GridLayout(2, false));
        dependencyContractsGroup.setText("Dependency Contracts");
        dependencyContractsOnButton = new Button(dependencyContractsGroup, SWT.RADIO);
        dependencyContractsOnButton.setText("O&n");
        dependencyContractsOffButton = new Button(dependencyContractsGroup, SWT.RADIO);
        dependencyContractsOffButton.setText("O&ff");
        Group queryTreatmentGroup = new Group(proofSearchStrategyOptionComposite, SWT.NONE);
        queryTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        queryTreatmentGroup.setLayout(new GridLayout(2, false));
        queryTreatmentGroup.setText("Query Treatment");
        queryTreatmentOnButton = new Button(queryTreatmentGroup, SWT.RADIO);
        queryTreatmentOnButton.setText("On");
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
        labelProvider = new AutomaticProofLabelProvider();
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
        buttonComposite.setLayout(new GridLayout(3, false));
        Button exportButton = new Button(buttonComposite, SWT.PUSH);
        exportButton.setText("&Export");
        exportButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                exportProofs();
            }
        });
        Button startProofsButton = new Button(buttonComposite, SWT.PUSH);
        startProofsButton.setText("&Start all proofs");
        startProofsButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        startProofsButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                startProofs();
            }
        });
        Button openKeYButton = new Button(buttonComposite, SWT.PUSH);
        openKeYButton.setText("&Open KeY");
        openKeYButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                openKeY();
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
       long branches = 0;
       long nodes = 0;
       long time = 0;
       int closedCount = 0;
       for (AutomaticProof proof : proofs) {
          branches += proof.getBranches();
          nodes += proof.getNodes();
          time += proof.getTime();
          if (AutomaticProofResult.CLOSED.equals(proof.getResult())) {
             closedCount ++;
          }
       }
       // Compute sum text to show
       StringBuffer sb = new StringBuffer();
       sb.append(proofResultColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(closedCount);
       sb.append(" / ");
       sb.append(proofs.size());
       sb.append(" ");
       sb.append(AutomaticProofResult.CLOSED.getDisplayText());
       sb.append(", ");
       sb.append(proofNodesColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(nodes);
       sb.append(", ");
       sb.append(proofBranchesColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(branches);
       sb.append(", ");
       sb.append(proofTimeColumn.getColumn().getText());
       sb.append(" = ");
       sb.append(time);
       sb.append(", ");
       sb.append(proofTimeColumn.getColumn().getText());
       sb.append(" + ");
       sb.append(loadLabel.getText());
       sb.append(" = ");
       sb.append(loadingTime + time);
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
            final List<?> input = (List<?>)proofViewer.getInput();
            final boolean expandMethods = methodTreatmentExpandButton.getSelection();
            final boolean useDependencyContracts = dependencyContractsOnButton.getSelection();
            final boolean useQuery = queryTreatmentOnButton.getSelection();
            final boolean useDefOps = arithmeticTreatmentDefOpsButton.getSelection();
            new AbstractKeYMainWindowJob("Proving") {
                @Override
                protected IStatus run(IProgressMonitor monitor) {
                    try {
                        SWTUtil.checkCanceled(monitor);
                        monitor.beginTask("Proving", input.size());
                        for (Object obj : input) {
                            SWTUtil.checkCanceled(monitor);
                            if (obj instanceof AutomaticProof) {
                                ((AutomaticProof)obj).startProof(expandMethods, useDependencyContracts, useQuery, useDefOps);
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
                        Display.getDefault().syncExec(new Runnable() {
                           @Override
                           public void run() {
                              setProofSearchStrategyOptionsEnabled(true);
                           }
                        });
                    }
                }
            }.schedule();
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
            final boolean showKeYMainWindow = showKeYWindowButton.getSelection();
            if (location.exists()) {
                new AbstractKeYMainWindowJob("Loading in KeY") {
                    @Override
                    protected IStatus run(IProgressMonitor monitor) {
                       final long loadStartTime = System.currentTimeMillis();
                        try {
                            // Remove old proofs
                            if (proofs != null) {
                               for (AutomaticProof proof : proofs) {
                                  proof.removeProofEnvFromKeY();
                               }
                            }
                            // Unload old source
                            Display.getDefault().syncExec(new Runnable() {
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
                            SWTUtil.checkCanceled(monitor);
                            monitor.beginTask("Loading in KeY", IProgressMonitor.UNKNOWN);
                            InitConfig init = KeYUtil.internalLoad(location, null, null, showKeYMainWindow);
                            Services services = init.getServices();
                            boolean skipLibraryClasses = true;
                            // get all classes
                            SWTUtil.checkCanceled(monitor);
                            final Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
                            monitor.beginTask("Filtering types", kjts.size());
                            final Iterator<KeYJavaType> it = kjts.iterator();
                            while (it.hasNext()) {
                                SWTUtil.checkCanceled(monitor);
                               KeYJavaType kjt = it.next();
                               if (!(kjt.getJavaType() instanceof ClassDeclaration || 
                                     kjt.getJavaType() instanceof InterfaceDeclaration) || 
                                   (((TypeDeclaration)kjt.getJavaType()).isLibraryClass() && skipLibraryClasses)) {
                                  it.remove();
                               }
                               monitor.worked(1);
                            }
                            monitor.done();
                            // sort classes alphabetically
                            SWTUtil.checkCanceled(monitor);
                            monitor.beginTask("Sorting types", IProgressMonitor.UNKNOWN);
                            final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
                            Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
                               public int compare(KeYJavaType o1, KeYJavaType o2) {
                                  return o1.getFullName().compareTo(o2.getFullName());
                               }
                            });
                            monitor.done();
                            // List all contracts
                            SWTUtil.checkCanceled(monitor);
                            proofs = new LinkedList<AutomaticProof>();
                            monitor.beginTask("Analysing types", kjtsarr.length);
                            for (KeYJavaType type : kjtsarr) {
                                SWTUtil.checkCanceled(monitor);
                                ImmutableSet<ObserverFunction> targets = services.getSpecificationRepository().getContractTargets(type);
                                for (ObserverFunction target : targets) {
                                    ImmutableSet<Contract> contracts = services.getSpecificationRepository().getContracts(type, target);
                                    for (Contract contract : contracts) {
                                        proofs.add(new AutomaticProof(type.getFullName(), ClassTree.getDisplayName(services, contract.getTarget()), contract.getDisplayName(), init, contract));
                                    }
                                }
                                monitor.worked(1);
                            }
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
            Boolean showKeYWindow = memento.getBoolean(MEMENTO_KEY_SHOW_WINDOW);
            showKeYWindowButton.setSelection(showKeYWindow != null && showKeYWindow.booleanValue());
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
        }
    }

    /**
     * Saves the current state into the given {@link IMemento}.
     * @param memento The {@link IMemento} to save state in.
     */
    public void saveState(IMemento memento) {
        if (memento != null) {
            memento.putString(MEMENTO_KEY_LOCATION, locationText.getText());
            memento.putBoolean(MEMENTO_KEY_SHOW_WINDOW, showKeYWindowButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_EXPAND_METHODS, methodTreatmentExpandButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_USE_DEPENDENCY_CONTRACTS, dependencyContractsOnButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_USE_QUERY, queryTreatmentOnButton.getSelection());
            memento.putBoolean(MEMENTO_KEY_USE_DEF_OPS, arithmeticTreatmentDefOpsButton.getSelection());
        }
    }
}
