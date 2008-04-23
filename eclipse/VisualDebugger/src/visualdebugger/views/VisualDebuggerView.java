package visualdebugger.views;

import java.lang.reflect.InvocationTargetException;
import java.net.URL;

import javax.swing.SwingUtilities;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.action.*;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.*;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.*;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.part.ViewPart;
import org.osgi.framework.Bundle;

import visualdebugger.actions.StartVisualDebuggerAction;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.DebuggerListener;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;
import de.uka.ilkd.key.visualdebugger.executiontree.ITNode;

public class VisualDebuggerView extends ViewPart implements DebuggerListener {
    private TableViewer viewer;

    private Action runAction;

    private Action stepIntoAction;

    private Action stepOverAction;

    private Action doubleClickAction;

    private Action visualizeStateAction;

    private VisualDebugger vd = VisualDebugger.getVisualDebugger();

    private Shell shell;

    private StatusLineManager statusMgr;

    private String projectName;

    private Action showMainWindowAction;

    private Action allInvariants;

    private Action showImpliciteAttributes;

    private Action invariantsToPost;

    private Action quanSplitAction;

    /*
     * The content provider class is responsible for providing objects to the
     * view. It can wrap existing objects in adapters or simply return objects
     * as-is. These objects may be sensitive to the current input of the view,
     * or ignore it and always show the same content (like Task List, for
     * example).
     */

    class ViewContentProvider implements IStructuredContentProvider {
        public void inputChanged(Viewer v, Object oldInput, Object newInput) {
        }

        public void dispose() {
        }

        public Object[] getElements(Object parent) {
            if (parent == null)
                return new String[0];
            else if (parent instanceof ETNode) {
                ETNode n = (ETNode) parent;
                return (ITNode[]) n.getITNodesArray();
            } else if (parent instanceof ITNode[]) {
                return (ITNode[]) parent;

            }

            return new String[] { "One", "Two", "Three" };
        }
    }

    class ViewLabelProvider extends LabelProvider implements
            ITableLabelProvider {
        public String getColumnText(Object obj, int index) {
            if (obj instanceof ITNode) {
                return vd.prettyPrint(((ITNode) obj).getPc());
            }
            return "";
        }

        public Image getColumnImage(Object obj, int index) {
            return getImage(obj);
        }

        public Image getImage(Object obj) {
            return null;
        }
    }

    class NameSorter extends ViewerSorter {
    }

    /**
     * The constructor.
     */
    public VisualDebuggerView() {
        VisualDebugger.getVisualDebugger().addListener(this);
    }

    /**
     * This is a callback that will allow us to create the viewer and initialize
     * it.
     */
    public void createPartControl(Composite parent) {
        shell = parent.getShell();
        GridLayout layout = new GridLayout();

        parent.setLayout(layout);
        GridData data = new GridData(GridData.FILL_BOTH);
        Label l = new Label(parent, SWT.BORDER);
        l.setText("Path Condition:");

        l
                .setToolTipText("Shows the path condition for the current selected node in the execution tree");
        l.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

        viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL
                | SWT.V_SCROLL);

        viewer.getControl().setLayoutData(data);

        viewer.setContentProvider(new ViewContentProvider());
        viewer.setLabelProvider(new ViewLabelProvider());
        viewer.setSorter(new NameSorter());
        // viewer.setInput(getViewSite()); //TODO ??

        // StatusLineManager m = new StatusLineManager();

        // this.getViewSite().;
        // this.getConfigurationElement().

        // this.getViewSite().getActionBars().getStatusLineManager().setMessage("asdfasdf");
        // StatusLineManager m = new StatusLineManager();
        // m.createControl(viewer.getControl().getParent());
        // m.setMessage("afasdfasdf");

        // SubStatusLineManager
        // statusLineManager=(SubStatusLineManager)(getViewSite().getActionBars().getStatusLineManager());
        // statusLineManager.setVisible(true);
        // statusLineManager.setMessage("I'm read !");

        // GridData gid = new GridData();
        // gid.horizontalAlignment = GridData.FILL;
        // gid.verticalAlignment = GridData.BEGINNING;
        // cmpTextEditor.setLayoutData(gid);

        statusMgr = new StatusLineManager();
        statusMgr.createControl(parent, SWT.BORDER);
        statusMgr.getControl().setLayoutData(
                new GridData(GridData.FILL_HORIZONTAL));
        statusMgr.setMessage("Ready");
        // statusMgr.getProgressMonitor().beginTask("Test Task", 100);
        // statusMgr.

        // Label lb=new Label((Composite)statusMgr.getControl(),SWT.NULL);
        // gid = new GridData();
        // gid.horizontalAlignment = GridData.FILL;
        // gid.verticalAlignment = GridData.BEGINNING;
        // statusMgr.getControl().setLayoutData(gid);
        makeActions();
        hookContextMenu();
        hookDoubleClickAction();
        contributeToActionBars();

        // getViewSite().getActionBars().getStatusLineManager().setMessage("adfasdfsa");
        // getViewSite().getActionBars().getStatusLineManager().update(true);
        // setStatus( "JFace Example v1.0" );
    }

    private void hookContextMenu() {
        MenuManager menuMgr = new MenuManager("#PopupMenu");
        menuMgr.setRemoveAllWhenShown(true);
        menuMgr.addMenuListener(new IMenuListener() {
            public void menuAboutToShow(IMenuManager manager) {
                VisualDebuggerView.this.fillContextMenu(manager);
            }
        });
        Menu menu = menuMgr.createContextMenu(viewer.getControl());

        viewer.getControl().setMenu(menu);
        getSite().registerContextMenu(menuMgr, viewer);
    }

    private void setStatusMessage(final String message) {
        Display display = shell.getDisplay();
        final Thread barThread = new Thread("PBarThread") {
            public void run() {
                statusMgr.setMessage(message);
            }
        };
        display.asyncExec(barThread);

    }

    private void contributeToActionBars() {
        IActionBars bars = getViewSite().getActionBars();
        fillLocalPullDown(bars.getMenuManager());
        fillLocalToolBar(bars.getToolBarManager());
    }

    private void fillLocalPullDown(IMenuManager manager) {
        // Main.getInstance().isV
        // manager.add(this.invariantsToPost);
        manager.add(this.quanSplitAction);
        manager.add(this.allInvariants);
        manager.add(this.showImpliciteAttributes);
        manager.add(new Separator());
        manager.add(showMainWindowAction);

        // manager.add(stepIntoAction);
    }

    private void fillContextMenu(IMenuManager manager) {
        manager.add(visualizeStateAction);
        // manager.add(stepIntoAction);
        // // Other plug-ins can contribute there actions here
        manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
    }

    private void fillLocalToolBar(IToolBarManager manager) {
        manager.add(runAction);
        manager.add(stepIntoAction);
        manager.add(stepOverAction);
        // manager.add(this.removeRed); TODO
        // manager.add(testCaseAction);
    }

    private void makeActions() {
        runAction = new Action() {
            public void run() {
                vd.run();
                // Goal g = ip.getProof().
                // goal/Ruleappindex/clear,fill caches..

                // showMessage("Action 1 executed");
            }
        };
        runAction.setText("Run");
        runAction.setToolTipText("Run " + vd.getRunLimit() + " statements");
        runAction.setImageDescriptor(getImageDescriptor("run_exc.gif"));

        stepIntoAction = new Action() {
            public void run() {
                vd.stepInto();
                // showMessage("Step Into");
            }
        };
        stepIntoAction.setText("Step Into");
        stepIntoAction.setToolTipText("Step Into");
        stepIntoAction
                .setImageDescriptor(getImageDescriptor("stepinto_co.gif"));

        stepOverAction = new Action() {
            public void run() {
                vd.stepOver();
            }
        };
        stepOverAction.setText("Step Over");
        stepOverAction.setToolTipText("Step Over");
        stepOverAction
                .setImageDescriptor(getImageDescriptor("stepover_co.gif"));

        showMainWindowAction = new Action("KeY-Prover Window",
                IAction.AS_CHECK_BOX) {
            public void run() {
                final boolean isChecked = this.isChecked();
                if (SwingUtilities.isEventDispatchThread()) {
                    Main.getInstance(false).setVisible(isChecked);
                } else {
                    SwingUtilities.invokeLater(new Runnable() {
                        public void run() {                            
                            Main.getInstance(false).setVisible(isChecked);
                        }
                    });
                }
                // Main.getInstance().toFront();
                VisualDebugger.showMainWindow = this.isChecked();
            }
        };
        showMainWindowAction.setChecked(false);
        // showMainWindowAction.setText("KeY-Prover");
        showMainWindowAction
        .setToolTipText("Shows the KeY-Prover which runs in the background");

        quanSplitAction = new Action(
                "Quantifier Instantiation with Splitting ", Action.AS_CHECK_BOX) {
            public void run() {
                VisualDebugger.quan_splitting = this.isChecked();

            }
        };
        quanSplitAction.setChecked(false);
        // showMainWindowAction.setText("KeY-Prover");
        // quanSplitAction.setToolTipText("Shows the KeY-Prover which runs in
        // the background");

        this.allInvariants = new Action("Use all Invariants",
                Action.AS_CHECK_BOX) {
            public void run() {
                StartVisualDebuggerAction.allInvariants = allInvariants
                        .isChecked();

            }
        };
        allInvariants.setChecked(false);
        // allInvariants.setText("KeY-Prover");
        allInvariants
                .setToolTipText("Adds all class invariants to the precondition");

        this.showImpliciteAttributes = new Action("Show Implicite Attributes",
                Action.AS_CHECK_BOX) {
            public void run() {
                VisualDebugger.showImpliciteAttr = showImpliciteAttributes
                        .isChecked();

            }
        };
        showImpliciteAttributes.setChecked(false);
        visualizeStateAction = new Action() {
            public void run() {
                ISelection selection = viewer.getSelection();
                Object obj = ((IStructuredSelection) selection)
                        .getFirstElement();
                if (obj instanceof ITNode) {
                    vd.visualize((ITNode) obj);
                }
            }
        };
        visualizeStateAction.setText("Visualize State");

        doubleClickAction = new Action() {
            public void run() {
                ISelection selection = viewer.getSelection();
                Object obj = ((IStructuredSelection) selection)
                        .getFirstElement();

                // vd.visualize(null);
                if (obj instanceof ITNode) {

                    vd.getMediator().getSelectionModel().setSelectedNode(
                            ((ITNode) obj).getNode());
                }
                // showMessage("Double-click detected on "+obj.toString());
            }
        };
    }

    public void setInputThreadSave(final Object input) {
        Display display = shell.getDisplay();
        final Thread barThread = new Thread("PBarThread") {
            public void run() {
                viewer.setInput(input);
            }
        };
        display.asyncExec(barThread);
    }

    private void hookDoubleClickAction() {
        viewer.addDoubleClickListener(new IDoubleClickListener() {
            public void doubleClick(DoubleClickEvent event) {

                doubleClickAction.run();
            }
        });
    }

    private void showMessage(String message) {
        MessageDialog.openInformation(viewer.getControl().getShell(),
                "Visual Debugger", message);
    }

    protected StatusLineManager createStatusLineManager() {
        StatusLineManager slm = new StatusLineManager();
        slm.setMessage("TODO STATUSLINE!");
        slm.setErrorMessage("message");
        // slm.

        return slm;
    }

    public synchronized void update(DebuggerEvent event) {
        if (event.getType() == DebuggerEvent.PROJECT_LOADED_SUCCESSFUL) {
            this.projectName = (String) event.getSubject();
            setStatusMessage(projectName);
            this.setInputThreadSave(null);
        } else if (event.getType() == DebuggerEvent.EXEC_FINISHED) {
            setStatusMessage(projectName);
        } else if (event.getType() == DebuggerEvent.EXEC_STARTED) {
            setStatusMessage(projectName + ":  Running...");
        } else

        if (event.getType() == DebuggerEvent.NODE_SELECTED) {
            setInputThreadSave(event.getSubject());
            ETNode ll = (ETNode) event.getSubject();

            // vd.removeRedundandPC(ll.getITNodes());
        } else if (event.getType() == DebuggerEvent.RED_PC_REMOVED) {
            setInputThreadSave(event.getSubject());
        }
    }

    /**
     * Passing the focus request to the viewer's control.
     */
    public void setFocus() {
        viewer.getControl().setFocus();
    }

    private ImageDescriptor getImageDescriptor(String file) {
        ImageDescriptor image = null;
        try {
            String filename = "icons/" + file;
            Bundle bun = Platform.getBundle("VisualDebugger");
            IPath ip = new Path(filename);
            URL url = FileLocator.find(bun, ip, null);

            URL resolved = FileLocator.resolve(url);

            image = ImageDescriptor.createFromURL(resolved);
        } catch (Exception e) {
            e.printStackTrace();
        }

        return image;
    }

}
