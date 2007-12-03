package visualdebugger.views;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.HashMap;
import java.util.Map;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JTextArea;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.LightweightSystem;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jface.action.*;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.viewers.*;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowData;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.ProgressBar;
import org.eclipse.swt.widgets.Scale;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.*;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.MarkerUtilities;

import visualdebugger.views.ExecutionTreeView.PM;

import de.uka.ilkd.key.visualdebugger.*;
import de.uka.ilkd.key.visualdebugger.executiontree.*;

/**
 * The Class WatchpointView.
 */
public class WatchpointView extends ViewPart {

	/** The viewer. */
	private TableViewer viewer;

	/** The delete action. */
	private Action removeAction;

	/** The add action. */
	private Action addAction;

	/** The bp manager. */
	private BreakpointManager bpManager;

	private Composite parent;

	/**
	 * The Class BpContentProvider.
	 */
	class BpContentProvider implements IStructuredContentProvider {

		/**
		 * Input changed.
		 * 
		 * @param v
		 *            the v
		 * @param oldInput
		 *            the old input
		 * @param newInput
		 *            the new input
		 */
		public void inputChanged(Viewer v, Object oldInput, Object newInput) {
		}

		/**
		 * Dispose.
		 */
		public void dispose() {
		}

		/**
		 * Gets the elements.
		 * 
		 * @param parent
		 *            the parent
		 * 
		 * @return the elements
		 */
		public Object[] getElements(Object parent) {
			if (parent instanceof BreakpointManager) {
				return ((BreakpointManager) parent).getBreapoints();
			} else
				return new String[] { "One", "Two", "Three" };
		}
	}

	/**
	 * The Class BpLabelProvider.
	 */
	class BpLabelProvider extends LabelProvider implements ITableLabelProvider {

		/**
		 * Gets the column text.
		 * 
		 * @param obj
		 *            the obj
		 * @param index
		 *            the index
		 * 
		 * @return the column text
		 */
		public String getColumnText(Object obj, int index) {
			if (obj instanceof BreakpointEclipse) {
				BreakpointEclipse b = (BreakpointEclipse) obj;
				if (index == 2) {
					final String s = b.getStatement().toString();
					return s.substring(0, s.lastIndexOf("\n"));
				} else if (index == 0) {
					return b.getCompilationUnit().getResource().getName();
				} else if (index == 1) {
					return b.getMethod().getElementName();
				}

				return b.getId().getId() + "";
			}
			return "UNKNOWN CONTENT";
		}

		/**
		 * Gets the column image.
		 * 
		 * @param obj
		 *            the obj
		 * @param index
		 *            the index
		 * 
		 * @return the column image
		 */
		public Image getColumnImage(Object obj, int index) {
			return null;
		}

		/**
		 * Gets the image.
		 * 
		 * @param obj
		 *            the obj
		 * 
		 * @return the image
		 */
		public Image getImage(Object obj) {
			return PlatformUI.getWorkbench().getSharedImages().getImage(
					ISharedImages.IMG_OBJ_ELEMENT);
		}
	}

	/**
	 * Instantiates a new breakpoint view.
	 */
	public WatchpointView() {
		bpManager = VisualDebugger.getVisualDebugger().getBpManager();
	}

	/**
	 * This is a callback that will allow us to create the viewer and initialize
	 * it.
	 * 
	 * @param parent
	 *            the parent
	 */
	public void createPartControl(Composite parent) {
		Composite shell = parent.getShell();
		this.parent = parent;
		// create left side of the view window
		parent.setLayout(new GridLayout(2, false));
		viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL
				| SWT.V_SCROLL | SWT.SEPARATOR);

		// viewer.setSorter(new NameSorter());

		Table table = viewer.getTable();
	    table.setLayoutData(new GridData(GridData.FILL_BOTH));
		TableColumn column;

		column = new TableColumn(table, SWT.NONE, 0);
		column.setWidth(200);
		column.setText("Watch Expression");
		column = new TableColumn(table, SWT.NONE, 1);
		column.setWidth(100);
		column.setText("File");
		column = new TableColumn(table, SWT.NONE, 2);
		column.setWidth(100);
		column.setText("Method");
		column = new TableColumn(table, SWT.NONE, 3);
		column.setWidth(70);
		column.setText("Statement");
		table.setHeaderVisible(true);
		table.setLinesVisible(true);
		viewer.setContentProvider(new BpContentProvider());
		viewer.setLabelProvider(new BpLabelProvider());

		viewer.setInput(bpManager);
		
		hookShell();
		hookListener();
		makeActions();
		hookContextMenu();

		contributeToActionBars();
	}

	private void hookShell() {
		
		Composite localShell = new Composite(parent, 0);
		// localShell.set
		GridData gdata = new GridData(GridData.FILL_VERTICAL);
		// gdata.minimumWidth=30;
		// gdata.grabExcessHorizontalSpace=true;
		localShell.setLayoutData(gdata);

		localShell.setLayout(new GridLayout());

		Group progressGroup = new Group(localShell, 0);
		RowLayout progressGroupLayout = new RowLayout(
				org.eclipse.swt.SWT.HORIZONTAL);
		progressGroup.setLayout(progressGroupLayout);
		GridData progressGroupLData = new GridData();
		progressGroupLData.widthHint = 237;
		progressGroupLData.heightHint = 23;
		progressGroup.setLayoutData(progressGroupLData);
		progressGroup.setText("Progress");

		RowData progressBar1LData = new RowData();



		Group rootGroup = new Group(localShell, 0);
		rootGroup.setText("Properties");
		FontData data = rootGroup.getFont().getFontData()[0];
		data.setStyle(SWT.BOLD);
		rootGroup.setLayout(new GridLayout());
		GridData rootGroupLData = new GridData();
		rootGroupLData.widthHint = 237;
		rootGroupLData.heightHint = 112;
		rootGroup.setLayoutData(rootGroupLData);


		Group bcGroup = new Group(localShell, 0);
		bcGroup.setBackground(ColorConstants.white);
		bcGroup.setText("Branch Condition");

		GridData bcGroupLData = new GridData();
		bcGroupLData.verticalAlignment = GridData.FILL;
		bcGroupLData.horizontalAlignment = GridData.FILL;
		bcGroupLData.grabExcessHorizontalSpace = true;
		bcGroupLData.grabExcessVerticalSpace = true;
		bcGroup.setLayoutData(bcGroupLData);
		bcGroup.setLayout(new GridLayout());
		
	}

	/**
	 * Hook listener.
	 */
	private void hookListener() {
		viewer.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				// if the selection is empty clear the label
				if (event.getSelection().isEmpty()) {

					return;
				}
				if (event.getSelection() instanceof IStructuredSelection) {
					IStructuredSelection selection = (IStructuredSelection) event
							.getSelection();

					Object domain = selection.getFirstElement();
					if (domain instanceof BreakpointEclipse) { // TODO !!!!!
						BreakpointEclipse bp = (BreakpointEclipse) domain;
						// ICompilationUnit unit = bp.getCompilationUnit();
						ISourceViewer viewer = null;
						IWorkbench workbench = PlatformUI.getWorkbench();
						IWorkbenchPage page = workbench
								.getActiveWorkbenchWindow().getActivePage();
						IMarker marker = null;
						// TODO add marker attribute to BreakpointEclipse
						try {
							IMarker[] markers = bp.getCompilationUnit()
									.getResource().findMarkers(
											"VisualDebugger.bpmarker", true, 1);
							for (int i = 0; i < markers.length; i++) {

								if (((Integer) markers[i]
										.getAttribute("StatementId"))
										.intValue() == bp.getId().getId()) {
									marker = markers[i];
								}
							}
						} catch (CoreException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}

						try {
							IEditorPart ed = org.eclipse.ui.ide.IDE.openEditor(
									page, marker, true);
							viewer = (ISourceViewer) ed
									.getAdapter(ITextOperationTarget.class);
						} catch (Exception e) {
							e.printStackTrace();

						}

						// IEditorPart editor
						// =PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
						/*
						 * //bp.getAnnotation().getSourceViewer().setSelectedRange(bp.getSelection().getOffset(),
						 * bp.getSelection().getLength()); if (editor instanceof
						 * ITextEditor){ ITextEditor tedit= (ITextEditor)
						 * editor;
						 * tedit.getSelectionProvider().setSelection(bp.getSelection()); }
						 */

					}
				}
			}
		});
	}

	/**
	 * Hook context menu.
	 */
	private void hookContextMenu() {
		MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);
		menuMgr.addMenuListener(new IMenuListener() {
			public void menuAboutToShow(IMenuManager manager) {
				WatchpointView.this.fillContextMenu(manager);
			}
		});
		Menu menu = menuMgr.createContextMenu(viewer.getControl());
		viewer.getControl().setMenu(menu);
		getSite().registerContextMenu(menuMgr, viewer);
	}

	/**
	 * Contribute to action bars.
	 */
	private void contributeToActionBars() {
		IActionBars bars = getViewSite().getActionBars();
		fillLocalPullDown(bars.getMenuManager());
		fillLocalToolBar(bars.getToolBarManager());
	}

	/**
	 * Fill local pull down.
	 * 
	 * @param manager
	 *            the manager
	 */
	private void fillLocalPullDown(IMenuManager manager) {

		manager.add(addAction);
		manager.add(new Separator());
		manager.add(removeAction);
	}

	/**
	 * Fill context menu.
	 * 
	 * @param manager
	 *            the manager
	 */
	private void fillContextMenu(IMenuManager manager) {
		manager.add(addAction);
		manager.add(removeAction);
		// Other plug-ins can contribute there actions here
		manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
	}

	/**
	 * Fill local tool bar.
	 * 
	 * @param manager
	 *            the manager
	 */
	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(addAction);
		manager.add(removeAction);
	}

	/**
	 * Make actions.
	 */
	private void makeActions() {
		addAction = new Action() {
			public void run() {
				
				//TODO

			}

		};
		addAction.setText("Add");
		addAction.setToolTipText("Adds an expression that should be watched");

		removeAction = new Action() {
			public void run() {

					// TODO
			}

		};
		removeAction.setText("Remove");
		removeAction.setToolTipText("Remove watchpoint");

	}

	/**
	 * Passing the focus request to the viewer's control.
	 */
	public void setFocus() {
		viewer.getControl().setFocus();
	}
}