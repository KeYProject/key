/**
 * 
 */
package org.key_project.sed.ui.management;

import java.util.ArrayList;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IPageListener;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.util.eclipse.swt.SWTUtil;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * @author Leonard Goetz
 *
 */
public class SEDSelectionManager {

	public static final SEDSelectionManager instance = new SEDSelectionManager();
	
	private ArrayList<KeYEditor> selectionModels = new ArrayList<>();

	private final ISelectionChangedListener selectionListener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			handleSelectionChanged(event);

		}
	};

	private final IWindowListener windowListener = new IWindowListener() {
		@Override
		public void windowActivated(IWorkbenchWindow window) {
		}

		@Override
		public void windowDeactivated(IWorkbenchWindow window) {
		}

		@Override
		public void windowClosed(IWorkbenchWindow window) {
			handleWindowClosed(window);
		}

		@Override
		public void windowOpened(IWorkbenchWindow window) {
			handleWindowOpened(window);
		}
	};

	private final IPageListener pageListener = new IPageListener() {
		@Override
		public void pageOpened(IWorkbenchPage page) {
			handlePageOpened(page);
		}

		@Override
		public void pageClosed(IWorkbenchPage page) {
			handlePageClosed(page);
		}

		@Override
		public void pageActivated(IWorkbenchPage page) {
		}
	};

	private final IPartListener partListener = new IPartListener() {

		@Override
		public void partOpened(IWorkbenchPart part) {
			handlePartOpened(part);
		}

		@Override
		public void partDeactivated(IWorkbenchPart part) {
		}

		@Override
		public void partClosed(IWorkbenchPart part) {
			handlePartClosed(part);
		}

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
		}

		@Override
		public void partActivated(IWorkbenchPart part) {
		}
	};

	private SEDSelectionManager() {

	}

	public void start() {
		IWorkbench workbench = PlatformUI.getWorkbench();
		workbench.addWindowListener(windowListener);
		for (IWorkbenchWindow window : workbench.getWorkbenchWindows()) {
			init(window);
		}
	}

	private void init(IWorkbenchWindow window) {
		window.addPageListener(pageListener);
		for (IWorkbenchPage page : window.getPages()) {
			init(page);
		}
	}

	private void init(IWorkbenchPage page) {
		page.addPartListener(partListener);
		for (IEditorReference reference: page.getEditorReferences()) {
			IEditorPart editor = reference.getEditor(false);
			if (editor != null) {
				init(editor);
			}
		}
		for (IViewReference reference : page.getViewReferences()) {
			IViewPart view = reference.getView(false);
			if (view != null) {
				init(view);
			}
		}
	}

	private void init(final IViewPart view) {
		if (view instanceof IDebugView) {
			IDebugView debugView = (IDebugView) view;
			if (debugView.getSite().getId().equals(IDebugUIConstants.ID_DEBUG_VIEW)) {
				debugView.getSite().getSelectionProvider().addSelectionChangedListener(selectionListener);
			}
		}
	}
	
	private void init(final IEditorPart editor) {
		if (editor instanceof KeYEditor) {
			KeYEditor keyEditor = (KeYEditor) editor;
			if (!selectionModels.contains(keyEditor)) {
				selectionModels.add(keyEditor);
			}
		}
	}

	public void stop() {
		IWorkbench workbench = PlatformUI.getWorkbench();
		workbench.removeWindowListener(windowListener);
		for (IWorkbenchWindow window : workbench.getWorkbenchWindows()) {
			deinit(window, false);
		}
	}

	private void deinit(IWorkbenchWindow window, boolean closing) {
		window.removePageListener(pageListener);
		for (IWorkbenchPage page : window.getPages()) {
			deinit(page, closing);
		}
	}

	private void deinit(IWorkbenchPage page, boolean closing) {
		page.removePartListener(partListener);
		for (IEditorReference reference: page.getEditorReferences()) {
			IEditorPart editor = reference.getEditor(false);
			if (editor != null) {
				deinit(editor, closing);
			}
		}
		for (IViewReference reference : page.getViewReferences()) {
			IViewPart view = reference.getView(false);
			if (view != null) {
				deinit(view, closing);
			}
		}
	}

	private void deinit(final IViewPart view, boolean closing) {
		if (!closing) {
			if (view instanceof IDebugView) {
				IDebugView debugView = (IDebugView) view;
				if (debugView.getSite().getId().equals(IDebugUIConstants.ID_DEBUG_VIEW)) {
					debugView.getSite().getSelectionProvider().removeSelectionChangedListener(selectionListener);
				}
			}
		}
	}
	
	private void deinit(final IEditorPart editor, boolean closing) {
		if (editor instanceof KeYEditor) {
			selectionModels.remove(editor);
		}
	}

	private void handleWindowOpened(IWorkbenchWindow window) {
		init(window);
	}

	private void handleWindowClosed(IWorkbenchWindow window) {
		deinit(window, true);
	}

	private void handlePageOpened(IWorkbenchPage page) {
		init(page);
	}

	private void handlePageClosed(IWorkbenchPage page) {
		deinit(page, true);
	}

	private void handlePartOpened(IWorkbenchPart part) {
		if (part instanceof IEditorPart) {
			init((IEditorPart) part);
		} else if (part instanceof IViewPart) {
			init((IViewPart) part);
		}
	}

	private void handlePartClosed(IWorkbenchPart part) {
		if (part instanceof IEditorPart) {
			deinit((IEditorPart) part, true);
		} else if (part instanceof IViewPart) {
			deinit((IViewPart) part, true);
		}
	}

	private void handleSelectionChanged(SelectionChangedEvent event) {
		Object selection = SWTUtil.getFirstElement(event.getSelection());
		if (selection instanceof IKeYSENode<?>) {
			IKeYSENode<?> node = (IKeYSENode<?>) selection;
			IExecutionNode<?> exeNode = (IExecutionNode<?>) node.getExecutionNode();
			for (KeYEditor editor: selectionModels) {
				if (editor.getCurrentProof() == exeNode.getProof()) {
					editor.getSelectionModel().setSelectedNode(exeNode.getProofNode());
				}
			}
		}
	}

	/**
	 * Returns the only instance of this class.
	 * 
	 * @return The only instance of this class.
	 */
	public static SEDSelectionManager getInstance() {
		return instance;
	}
}
