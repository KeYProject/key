package visualdebugger.views;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.WatchPoint;
import de.uka.ilkd.key.visualdebugger.WatchPointManager;

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

	/** The watch point manager. */
	private WatchPointManager watchPointManager;

	private VisualDebugger vd = null;

	/**
	 * The Class WatchPointContentProvider.
	 */
	class WatchPointContentProvider implements IStructuredContentProvider {

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
		 */
		public Object[] getElements(Object inputElement) {

			WatchPointManager wpm = (WatchPointManager) inputElement;
			return wpm.getWatchPointsAsArray();
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
		 */
		public void dispose() {
			// TODO Auto-generated method stub

		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer,
		 *      java.lang.Object, java.lang.Object)
		 */
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
			// TODO Auto-generated method stub

		}

	}

	/**
	 * The Class WatchPointLabelProvider.
	 */
	class WatchPointLabelProvider extends LabelProvider implements
			ITableLabelProvider {

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object,
		 *      int)
		 */
		public Image getColumnImage(Object element, int columnIndex) {
			// TODO Auto-generated method stub
			return null;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object,
		 *      int)
		 */
		public String getColumnText(Object element, int columnIndex) {
			String result = "";
			WatchPoint wp = (WatchPoint) element;
			switch (columnIndex) {
			case 0:
				result = wp.getExpression();
				break;
			case 1:
				result = wp.getMethod();
				break;
			case 2:
				result = wp.getStatement_line();
				break;
			case 3:
				result = wp.getTypeOfSource() ;
				break;
			default:
				break;
			}
			return result;
		}

	}

	/**
	 * Instantiates a new breakpoint view.
	 */
	public WatchpointView() {
		vd = VisualDebugger.getVisualDebugger();
	}

	/**
	 * This is a callback that will allow us to create the viewer and initialize
	 * it.
	 * 
	 * @param parent
	 *            the parent
	 */
	public void createPartControl(Composite parent) {

		watchPointManager = new WatchPointManager();
		viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL
				| SWT.V_SCROLL | SWT.SEPARATOR);

		Table table = createTable();
		table.setHeaderVisible(true);
		table.setLinesVisible(true);

		viewer.setContentProvider(new WatchPointContentProvider());
		viewer.setLabelProvider(new WatchPointLabelProvider());

		viewer.setInput(watchPointManager);

		makeActions();
		// hookContextMenu();

		contributeToActionBars();
	}

	/**
	 * Creates the table.
	 * 
	 * @return the table
	 */
	private Table createTable() {
		Table table = viewer.getTable();

		TableColumn column;

		column = new TableColumn(table, SWT.NONE, 0);
		column.setWidth(150);
		column.setText("Watch Expression");

		column = new TableColumn(table, SWT.NONE, 1);
		column.setWidth(100);
		column.setText("Method");

		column = new TableColumn(table, SWT.NONE, 2);
		column.setWidth(100);
		column.setText("Line");

		column = new TableColumn(table, SWT.NONE, 3);
		column.setWidth(100);
		column.setText("in Type");
		return table;
	}

	/**
	 * Hook context menu.
	 */
	/*
	 * private void hookContextMenu() { MenuManager menuMgr = new
	 * MenuManager("#PopupMenu"); menuMgr.setRemoveAllWhenShown(true);
	 * menuMgr.addMenuListener(new IMenuListener() { public void
	 * menuAboutToShow(IMenuManager manager) {
	 * WatchpointView.this.fillContextMenu(manager); } }); Menu menu =
	 * menuMgr.createContextMenu(viewer.getControl());
	 * viewer.getControl().setMenu(menu); getSite().registerContextMenu(menuMgr,
	 * viewer); }
	 */

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
			private Shell shell = new Shell();

			public void run() {

				String[] information = getWatchPointInf();
				if (information == null) {
					MessageDialog
							.openError(PlatformUI.getWorkbench()
									.getActiveWorkbenchWindow().getShell(),
									"Adding WatchPoint",
									"Please select a global field or a constant in the Java Editor");
				} else {
					WatchExpressionDialog dialog = new WatchExpressionDialog(
							shell, java.lang.Integer.parseInt(information[1]),
							information[3]);
					
					if (information != null) {
						
						String expression = dialog.open();
						
						if (expression != null) {

							watchPointManager.addWatchPoint(new WatchPoint(
									information[4], expression, information[0],
									information[1], information[2]));
							vd.setWatchPointManager(watchPointManager);
							viewer.refresh();
						}
					}
				}

			}

		};
		addAction.setText("Add");
		addAction.setToolTipText("Adds an expression that should be watched");

		removeAction = new Action() {
			public void run() {

				IStructuredSelection sel = (IStructuredSelection) viewer
						.getSelection();

				Object element = sel.getFirstElement();
				if (element instanceof WatchPoint) {

					watchPointManager.removeWatchPoint((WatchPoint) element);
					viewer.refresh();

				}
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

	/**
	 * Gets the watch point manager.
	 * 
	 * @return the watch point manager
	 */
	public WatchPointManager getWatchPointManager() {
		return watchPointManager;
	}

	/**
	 * Gets the WatchPoint information.
	 * 
	 * Collects the necessary information to create a watchpoint.
	 * 
	 * @return information where
	 * 
	 * information[0]= The name of the JavaElement where the WatchPoint was set.
	 * information[1]= The line offset where the text selection begins.
	 * information[2]= The type in which the WatchPoint was set (fully qualified name).
	 * information[3]= The actual the source code for validating the WatchPoint.
	 * information[4]= The unique name of the boolean variable that is used to validate the watchpoint.
	 */
	private String[] getWatchPointInf() {

		String[] information = new String[5];
		String varName = "myDummy";

		IEditorPart editor = PlatformUI.getWorkbench()
				.getActiveWorkbenchWindow().getActivePage().getActiveEditor();

		if (editor instanceof ITextEditor) {
			ITextEditor tedit = (ITextEditor) editor;

			ISelection sel = tedit.getSelectionProvider().getSelection();
			ITextSelection tsel = (ITextSelection) sel;
			// set current line
			information[1] = (1 + tsel.getEndLine()) + "";

			IFile file = (IFile) tedit.getEditorInput().getAdapter(IFile.class);

			ICompilationUnit unit = JavaCore.createCompilationUnitFrom(file);
			String source = "";
			information[2] = unit.findPrimaryType().getFullyQualifiedName();
			try {
				source = unit.getBuffer().getContents();

				while (source.indexOf(varName) > (-1)) {
					varName = varName.concat("x");
				}

			} catch (JavaModelException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			information[3] = source;
			information[4] = varName;

			try {
				IJavaElement je = unit.getElementAt(tsel.getOffset());

				if (je instanceof IField) {

					information[0] = je.getElementName();
				} else {

					return null;
				}

			} catch (JavaModelException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return information;
	}
}