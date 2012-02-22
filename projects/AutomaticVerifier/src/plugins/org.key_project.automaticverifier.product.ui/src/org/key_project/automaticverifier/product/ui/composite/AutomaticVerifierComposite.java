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
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IMemento;
import org.key_project.automaticverifier.product.ui.model.AutomaticProof;
import org.key_project.automaticverifier.product.ui.provider.AutomaticProofLabelProvider;
import org.key_project.automaticverifier.product.ui.util.LogUtil;
import org.key_project.automaticverifier.product.ui.view.AutomaticVerifierView;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

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
     * Constructor.
     * @param parent The parent {@link Composite}.
     * @param style The style to use.
     */
    public AutomaticVerifierComposite(Composite parent, int style) {
        super(parent, style);
        setLayout(new GridLayout(1, false));
        Group sourceGroup = new Group(this, SWT.NONE);
        sourceGroup.setText("Source");
        sourceGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        sourceGroup.setLayout(new GridLayout(1, false));
        Composite locationComposite = new Composite(sourceGroup, SWT.NONE);
        locationComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        locationComposite.setLayout(new GridLayout(2, false));
        Label locationLabel = new Label(locationComposite, SWT.NONE);
        locationLabel.setText("&Location");
        locationText = new Text(locationComposite, SWT.BORDER);
        locationText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        Composite loadComposite = new Composite(sourceGroup, SWT.NONE);
        loadComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        loadComposite.setLayout(new GridLayout(2, false)); 
        showKeYWindowButton = new Button(loadComposite, SWT.CHECK);
        showKeYWindowButton.setText("&Show KeY main window");
        Button loadSourceButton = new Button(loadComposite, SWT.PUSH);
        loadSourceButton.setText("&Load");
        loadSourceButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        loadSourceButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                loadSource();
            }
        });
        Group proofGroup = new Group(this, SWT.NONE);
        proofGroup.setText("Proofs");
        proofGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
        proofGroup.setLayout(new GridLayout(1, false));
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
        TableViewerColumn operationColumn = new TableViewerColumn(proofViewer, style);
        operationColumn.getColumn().setText("Operation");
        operationColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(operationColumn.getColumn(), new ColumnWeightData(15));
        TableViewerColumn contractColumn = new TableViewerColumn(proofViewer, style);
        contractColumn.getColumn().setText("Contract");
        contractColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(contractColumn.getColumn(), new ColumnWeightData(35));
        TableViewerColumn proofResultColumn = new TableViewerColumn(proofViewer, style);
        proofResultColumn.getColumn().setText("Proof Result");
        proofResultColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofResultColumn.getColumn(), new ColumnWeightData(15));
        TableViewerColumn proofNodesColumn = new TableViewerColumn(proofViewer, style);
        proofNodesColumn.getColumn().setText("Nodes");
        proofNodesColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofNodesColumn.getColumn(), new ColumnWeightData(5));
        TableViewerColumn proofBranchesColumn = new TableViewerColumn(proofViewer, style);
        proofBranchesColumn.getColumn().setText("Branches");
        proofBranchesColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofBranchesColumn.getColumn(), new ColumnWeightData(5));
        TableViewerColumn proofTimeColumn = new TableViewerColumn(proofViewer, style);
        proofTimeColumn.getColumn().setText("Time (milliseconds)");
        proofTimeColumn.getColumn().setMoveable(true);
        proofViewerLayout.setColumnData(proofTimeColumn.getColumn(), new ColumnWeightData(5));
        
        SWTUtil.makeTableColumnsSortable(proofViewer);
        proofViewer.setContentProvider(ArrayContentProvider.getInstance());
        proofViewer.setLabelProvider(new AutomaticProofLabelProvider());
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
     * Starts all available proofs.
     */
    public void startProofs() {
        if (proofViewer.getInput() instanceof List<?>) {
            final List<?> input = (List<?>)proofViewer.getInput();
            new Job("Proving") {
                @Override
                protected IStatus run(IProgressMonitor monitor) {
                    try {
                        SWTUtil.checkCanceled(monitor);
                        monitor.beginTask("Proving", input.size());
                        for (Object obj : input) {
                            SWTUtil.checkCanceled(monitor);
                            if (obj instanceof AutomaticProof) {
                                ((AutomaticProof)obj).startProof();
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
            // Unload old source
            proofViewer.setInput(Collections.EMPTY_LIST);
            // Load new source
            final File location = new File(locationText.getText());
            final boolean showKeYMainWindow = showKeYWindowButton.getSelection();
            if (location.exists()) {
                new Job("Loading in KeY") {
                    @Override
                    protected IStatus run(IProgressMonitor monitor) {
                        try {
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
                            final List<AutomaticProof> proofs = new LinkedList<AutomaticProof>();
                            monitor.beginTask("Analysing types", kjtsarr.length);
                            for (KeYJavaType type : kjtsarr) {
                                SWTUtil.checkCanceled(monitor);
                                // Get methods
                                ImmutableList<ProgramMethod> methods = services.getJavaInfo().getAllProgramMethodsLocallyDeclared(type);
                                listContracts(init, services, type, methods, proofs);
                                ImmutableList<ProgramMethod> constructors = services.getJavaInfo().getConstructors(type);
                                listContracts(init, services, type, constructors, proofs);
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
                        }
                    }
                    
                    protected void listContracts(InitConfig initConfig, Services services, KeYJavaType type, ImmutableList<ProgramMethod> methods, List<AutomaticProof> proofs) {
                        for (ProgramMethod pm : methods) {
                            if (!pm.isImplicit()) {
                                ImmutableSet<FunctionalOperationContract> operationContracts = services.getSpecificationRepository().getOperationContracts(type, pm);
                                for (FunctionalOperationContract oc : operationContracts) {
                                    proofs.add(new AutomaticProof(type.getFullName(), pm.getFullName(), oc.getName(), initConfig, oc));
                                }
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
            locationText.setText(memento.getString(MEMENTO_KEY_LOCATION));
            showKeYWindowButton.setSelection(memento.getBoolean(MEMENTO_KEY_SHOW_WINDOW));
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
        }
    }
}
