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

package org.key_project.keyide.ui.views;

import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.handlers.ShowSymbolicExecutionTreeOnlyHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.core.KeYSelectionModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

/**
 * A class to display the correct Outline for the current {@link Proof}
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan K�sdorf, Marco Drebing
 */
public class ProofTreeContentOutlinePage extends ContentOutlinePage implements
		ITabbedPropertySheetPageContributor {
	private final Proof proof;

	private final KeYEnvironment<?> environment;

	private LazyProofTreeContentProvider contentProvider;

	private ProofTreeLabelProvider labelProvider;

	private final KeYSelectionModel selectionModel;
	
	/**
	 * The {@link State} which indicates hiding or showing of intermediate proofsteps.
	 */
	private State hideState;
	
	/**
	 * The {@link State} for the show symbolic execution tree only outline filter.
	 */
	private State symbolicState;
	
	/**
	 * {@link KeYSelectionListener} to sync the KeYSelection with the
	 * {@link TreeSelection}.
	 */
	private final KeYSelectionListener listener = new KeYSelectionListener() {
		@Override
		public void selectedProofChanged(KeYSelectionEvent e) {
			updateSelectedNodeThreadSafe();
		}

		@Override
		public void selectedNodeChanged(KeYSelectionEvent e) {
			if (e.getSource().getSelectedNode().proof() == proof) {
				updateSelectedNodeThreadSafe();
			}
		}
	};

	private final AutoModeListener autoModeListener = new AutoModeListener() {
		@Override
		public void autoModeStarted(ProofEvent e) {
			handleAutoModeStarted(e);
		}

		@Override
		public void autoModeStopped(ProofEvent e) {
			handleAutoModeStopped(e);
		}
	};
	
	/**
	 * The {@link IStateListener} to sync the hide intermediate proof steps toggleState with the outline page.
	 */
	private IStateListener hideStateListener = new IStateListener() {

		@Override
		public void handleStateChange(State state, Object oldValue) {
			handleHideStateChanged(state, oldValue);
		}
	};
	
	/**
	 * The {@link IStateListener} to sync the show symbolic execution tree only toggleState with the outline page.
	 */
	private IStateListener symbolicStateListener = new IStateListener(){

      @Override
      public void handleStateChange(State state, Object oldValue) {
    	  handleSymbolicStateChanged(state, oldValue);
      }
	};
	
	/**
	 * Constructor.
	 * 
	 * @param proof
	 *            The {@link Proof} for this Outline.
	 */
	public ProofTreeContentOutlinePage(Proof proof,
			KeYEnvironment<?> environment, KeYSelectionModel selectionModel) {
		this.proof = proof;
		this.environment = environment;
		this.selectionModel = selectionModel;
		selectionModel.addKeYSelectionListener(listener);
		
		ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
	      if (service != null) {
	         Command hideCmd = service.getCommand(HideIntermediateProofstepsHandler.COMMAND_ID);
	         if (hideCmd != null) {
	            hideState = hideCmd.getState(RegistryToggleState.STATE_ID);
	            if (hideState != null) {
	            	hideState.addListener(hideStateListener);
	            }
	         }
	         
	         Command symbolicCmd = service.getCommand(ShowSymbolicExecutionTreeOnlyHandler.COMMAND_ID);
	         if (symbolicCmd != null) {
	            symbolicState = symbolicCmd.getState(RegistryToggleState.STATE_ID);
	            if (symbolicState != null) {
	            	symbolicState.addListener(symbolicStateListener);
	            }
	         }
	      }
	}
	
	/**
	 * Handles a change in the state of the showSymbolicExecutionTree outline filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleSymbolicStateChanged(State state, Object oldValue) {
		contentProvider.setSymbolicState((boolean) state.getValue());
		getTreeViewer().setInput(proof);
		updateSelectedNodeThreadSafe();
	}

	/**
	 * Handles a change in the state of the hideIntermediateProofsteps outline filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleHideStateChanged(State state, Object oldValue) {
		contentProvider.setHideState((boolean) state.getValue());
		getTreeViewer().setInput(proof);
		updateSelectedNodeThreadSafe();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void dispose() {
		selectionModel.removeKeYSelectionListener(listener);
		environment.getProofControl().removeAutoModeListener(autoModeListener);
		if (contentProvider != null) {
			contentProvider.dispose();
		}
		if (labelProvider != null) {
			labelProvider.dispose();
		}
		
		if (hideState != null) {
			hideState.removeListener(hideStateListener);
		}
		
		if (symbolicState != null) {
			symbolicState.removeListener(symbolicStateListener);
		}
		
		super.dispose();
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	protected int getTreeStyle() {
		return SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void createControl(Composite parent) {
		// Create TreeViewer
		super.createControl(parent);
		getTreeViewer().setUseHashlookup(true);
		contentProvider = new LazyProofTreeContentProvider(environment.getProofControl());
		// initialize boolean flags for hideIntermediateProofSteps and showSymbolicExecutionTree outline filter
		contentProvider.setHideState((boolean) hideState.getValue());
		contentProvider.setSymbolicState((boolean) symbolicState.getValue());
		getTreeViewer().setContentProvider(contentProvider);
		labelProvider = new ProofTreeLabelProvider(getTreeViewer(), environment.getProofControl(), proof);
		getTreeViewer().setLabelProvider(labelProvider);
		getTreeViewer().setInput(proof);
		contentProvider.injectTopLevelElements();
      environment.getProofControl().addAutoModeListener(autoModeListener); // IMPORTANT: Needs to be registered after label provider is created. Otherwise, injecting elements during selection update fails.
		// Create context menu of TreeViewer
		MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
		Menu menu = menuManager.createContextMenu(getTreeViewer().getControl());
		getTreeViewer().getControl().setMenu(menu);
		getSite().registerContextMenu("org.key_project.keyide.ui.view.outline.popup", menuManager, getTreeViewer());
		updateSelectedNode();
	}

	/**
	 * When the auto mode starts.
	 * @param e The event.
	 */
	protected void handleAutoModeStarted(ProofEvent e) {
		// Ignore mediator selection changes while auto mode is running
		// (Behavior of original KeY UI and solves problem with selection
		// synchronization with the shown TreeViewer)
		selectionModel.removeKeYSelectionListener(listener);
	}

	/**
	 * When the auto mode stops.
	 * @param e The event.
	 */
	protected void handleAutoModeStopped(ProofEvent e) {
		if (e.getSource() == proof) {
			// Listen for mediator selection changes caused by the user to
			// synchronize them with the shown TreeViewer
			selectionModel.addKeYSelectionListener(listener);
			// Make sure that correct selected node is shown
			updateSelectedNodeThreadSafe();
		}
	}

	/**
	 * Executes {@link #updateSelectedNode()} asynchronously and thread safe.
	 */
	protected void updateSelectedNodeThreadSafe() {
		if (!getControl().getDisplay().isDisposed()) {
			getControl().getDisplay().asyncExec(new Runnable() {
				@Override
				public void run() {
					if (!getControl().isDisposed()) {
						updateSelectedNode();
					}
				}
			});
		}
	}

	/**
	 * Updates the selected node of the shown {@link TreeViewer} when the
	 * selection of the {@link KeYMediator} has changed.
	 */
	protected void updateSelectedNode() {
		Node mediatorNode = selectionModel.getSelectedNode();
		Object selectedNode = getSelectedNode();
		if (mediatorNode != selectedNode) {
			// Make sure that Node to select is loaded in lazy TreeViewer
			makeSureElementIsLoaded(mediatorNode);
			if (mediatorNode != null) {
	         Object parent = contentProvider.getParent(mediatorNode);
	         int viewIndex = contentProvider.getIndexOf(parent, mediatorNode);
	         // Select Node in lazy TreeViewer or the parent node when the node got filtered out
	         if (viewIndex >= 0) {
	            getTreeViewer().setSelection(SWTUtil.createSelection(mediatorNode), true);
	         }
            else {
	            getTreeViewer().setSelection(SWTUtil.createSelection(parent), true);
	         }
			}
			else {
            getTreeViewer().setSelection(StructuredSelection.EMPTY, true);
			}
		}
      else {
		   // scroll to the selected Node
			Object selectedObj = SWTUtil.getFirstElement(getSelection());
			if (selectedObj != null && !(selectedObj instanceof BranchFolder)) {
				getTreeViewer().reveal(selectedNode);
			}
		}
	}

   /**
    * Makes sure that the given {@link Node} is known by the shown
    * {@link TreeViewer}.
    * 
    * @param node
    *            The {@link Node} to make that is known by the shown
    *            {@link TreeViewer}.
    */
   public void makeSureElementIsLoaded(Node node) {
      makeSureElementIsLoaded(node, getTreeViewer(), contentProvider);
   }

	/**
	 * Makes sure that the given {@link Node} is known by the shown
	 * {@link TreeViewer}.
	 * 
	 * @param node
	 *            The {@link Node} to make that is known by the shown
	 *            {@link TreeViewer}.
	 */
	public static void makeSureElementIsLoaded(Node node, TreeViewer treeViewer, LazyProofTreeContentProvider contentProvider) {
		// Collect unknown parents
		Deque<Object> unknownParents = new LinkedList<Object>();
		boolean unknown = true;
		Object current = node;
		while (unknown && current != null) {
			if (treeViewer.testFindItem(current) == null) {
				unknownParents.addFirst(current);
			} else {
				unknown = false;
			}
			current = contentProvider.getParent(current);
		}
		// Inject unknown elements
		for (Object unknownElement : unknownParents) {
			Object parent = contentProvider.getParent(unknownElement);
			int viewIndex = contentProvider.getIndexOf(parent, unknownElement);
			if (viewIndex >= 0) {
            contentProvider.updateChildCount(parent, 0);
            contentProvider.updateElement(parent, viewIndex);
			}
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		// Change selected node of mediator only if content provider is not in
		// refresh phase after stopping the auto mode
		Node node = getSelectedNode(event.getSelection());
		Node mediatorNode = selectionModel.getSelectedNode();
		if (node != mediatorNode && node != null) {
			selectionModel.setSelectedNode(node);
		}
		
		// Fire event to listener
		super.selectionChanged(event);
	}

	/**
	 * Returns the selected {@link Node}.
	 * 
	 * @return The selected {@link Node} or {@code null} if no {@link Node} is
	 *         selected.
	 */
	protected Node getSelectedNode() {
		return getSelectedNode(getSelection());
	}

	/**
	 * Returns the selected {@link Node} provided by the given
	 * {@link ISelection}.
	 * 
	 * @param selection
	 *            The {@link ISelection} to extract selected {@link Node} from.
	 * @return The selected {@link Node} or {@code null} if no {@link Node} is
	 *         selected.
	 */
	protected Node getSelectedNode(ISelection selection) {
		Object selectedObj = SWTUtil.getFirstElement(selection);
		if (selectedObj instanceof Node) {
			return (Node) selectedObj;
		} else if (selectedObj instanceof BranchFolder) {
			return ((BranchFolder) selectedObj).getChild();
		} else {
			return null;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public String getContributorId() {
		return KeYEditor.CONTRIBUTOR_ID;
	}
}