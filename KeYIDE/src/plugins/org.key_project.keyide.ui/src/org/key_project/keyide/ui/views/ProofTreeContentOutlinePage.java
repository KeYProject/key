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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.util.SafeRunnable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.part.IPageSite;
import org.eclipse.ui.part.Page;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.key_project.keyide.ui.composite.SearchComposite;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.handlers.ShowSymbolicExecutionTreeOnlyHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.keyide.ui.util.AbstractProofNodeSearch;
import org.key_project.keyide.ui.util.AbstractProofNodeSearch.ISearchCallback;
import org.key_project.keyide.ui.util.IProofNodeSearchSupport;
import org.key_project.keyide.ui.util.ProofNodeTextSearch;
import org.key_project.keyide.ui.util.ProofTreeColorManager;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.ObservableTreeViewer;
import org.key_project.util.eclipse.swt.viewer.event.IViewerUpdateListener;
import org.key_project.util.eclipse.swt.viewer.event.ViewerUpdateEvent;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

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
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofTreeContentOutlinePage extends Page implements IContentOutlinePage, ISelectionChangedListener, ITabbedPropertySheetPageContributor, IProofNodeSearchSupport {
   /**
    * The registered {@link ISelectionChangedListener}.
    */
   private final List<ISelectionChangedListener> selectionChangedListeners = new LinkedList<ISelectionChangedListener>();
   
   /**
    * The used {@link ProofTreeColorManager}.
    */
   private ProofTreeColorManager proofTreeColorManager;
   
   private final Proof proof;

	private final KeYEnvironment<?> environment;

	private LazyProofTreeContentProvider contentProvider;

	private ProofTreeLabelProvider labelProvider;

	private final KeYSelectionModel selectionModel;
	
	/**
	 * The root {@link Composite} which contains all visible child composites.
	 */
	private Composite root;
	
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
	 * The used {@link ObservableTreeViewer} which shows the proof tree.
	 */
	private ObservableTreeViewer treeViewer;
	
	/**
	 * The used {@link SearchComposite}.
	 */
	private SearchComposite searchComposite;
	
	/**
	 * A search for proof nodes.
	 */
	private ProofNodeTextSearch searchJob;
	
	/**
	 * Constructor.
	 * @param proof The {@link Proof} for this Outline.
	 */
	public ProofTreeContentOutlinePage(Proof proof, 
	                                   KeYEnvironment<?> environment, 
	                                   KeYSelectionModel selectionModel) {
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
	 * {@inheritDoc}
	 */
	@Override
   public void init(IPageSite pageSite) {
      super.init(pageSite);
      pageSite.setSelectionProvider(this);
   }
	
	/**
	 * Handles a change in the state of the showSymbolicExecutionTree outline filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleSymbolicStateChanged(State state, Object oldValue) {
		contentProvider.setSymbolicState((boolean) state.getValue());
		treeViewer.setInput(proof);
		updateSelectedNodeThreadSafe();
	}

	/**
	 * Handles a change in the state of the hideIntermediateProofsteps outline filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleHideStateChanged(State state, Object oldValue) {
		contentProvider.setHideState((boolean) state.getValue());
		treeViewer.setInput(proof);
		updateSelectedNodeThreadSafe();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void dispose() {
      disposeSearch();
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
      if (proofTreeColorManager != null) {
         proofTreeColorManager.dispose();
      }
		super.dispose();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void createControl(Composite parent) {
      proofTreeColorManager = new ProofTreeColorManager(parent.getDisplay());
      proofTreeColorManager.addPropertyChangeListener(new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            handleProofTreeColorChanged();
         }
      });
      // Root composite
      GridLayout rootLayout = new GridLayout(1, false);
      rootLayout.horizontalSpacing = 0;
      rootLayout.marginBottom = 0;
      rootLayout.marginHeight = 0;
      rootLayout.marginLeft = 0;
      rootLayout.marginRight = 0;
      rootLayout.marginTop = 0;
      rootLayout.marginWidth = 0;
      rootLayout.verticalSpacing = 0;
      root = new Composite(parent, SWT.NONE);
      root.setLayout(rootLayout);
		// Create TreeViewer
	   treeViewer = new ObservableTreeViewer(root, SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL);
	   treeViewer.getTree().setLayoutData(new GridData(GridData.FILL_BOTH));
	   treeViewer.addSelectionChangedListener(this);
		treeViewer.setUseHashlookup(true);
		treeViewer.addViewerUpdateListener(new IViewerUpdateListener() {
         @Override
         public void itemUpdated(ViewerUpdateEvent e) {
            handleItemUpdated(e);
         }
      });
		contentProvider = new LazyProofTreeContentProvider(environment.getProofControl());
		// initialize boolean flags for hideIntermediateProofSteps and showSymbolicExecutionTree outline filter
		contentProvider.setHideState((boolean) hideState.getValue());
		contentProvider.setSymbolicState((boolean) symbolicState.getValue());
		treeViewer.setContentProvider(contentProvider);
		labelProvider = new ProofTreeLabelProvider(treeViewer, environment.getProofControl(), proof);
		treeViewer.setLabelProvider(labelProvider);
		treeViewer.setInput(proof);
		contentProvider.injectTopLevelElements();
      environment.getProofControl().addAutoModeListener(autoModeListener); // IMPORTANT: Needs to be registered after label provider is created. Otherwise, injecting elements during selection update fails.
		// Create context menu of TreeViewer
		MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
		Menu menu = menuManager.createContextMenu(treeViewer.getControl());
		treeViewer.getControl().setMenu(menu);
		getSite().registerContextMenu("org.key_project.keyide.ui.view.outline.popup", menuManager, treeViewer);
		updateSelectedNode();
	}

	/**
	 * When a color of the proof tree has changed.
	 */
	protected void handleProofTreeColorChanged() {
      treeViewer.refresh();
   }

   /**
	 * When a tree viewer item was updated.
	 * @param e The event.
	 */
	protected void handleItemUpdated(ViewerUpdateEvent e) {
	   TreeItem item = (TreeItem) e.getItem();
      if (item != null) {
         Object data = e.getElement();
         if (data instanceof Node) {
            proofTreeColorManager.colorProofTreeNode(item, (Node) data);
         }
      }
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
		if (!getControl().isDisposed()) {
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
	            treeViewer.setSelection(SWTUtil.createSelection(mediatorNode), true);
	         }
            else {
	            treeViewer.setSelection(SWTUtil.createSelection(parent), true);
	         }
			}
			else {
            treeViewer.setSelection(StructuredSelection.EMPTY, true);
			}
		}
      else {
		   // scroll to the selected Node
			Object selectedObj = SWTUtil.getFirstElement(getSelection());
			if (selectedObj != null && !(selectedObj instanceof BranchFolder)) {
				treeViewer.reveal(selectedNode);
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
      makeSureElementIsLoaded(node, treeViewer, contentProvider);
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
		fireSelectionChanged(event.getSelection());
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

	/**
	 * Returns the used {@link TreeViewer}.
	 * @return The used {@link TreeViewer} or {@code null} if not available.
	 */
   public TreeViewer getTreeViewer() {
      return treeViewer;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISelection getSelection() {
      return treeViewer != null ? 
             treeViewer.getSelection() : 
             StructuredSelection.EMPTY;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setSelection(ISelection selection) {
      if (treeViewer != null) {
         treeViewer.setSelection(selection);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addSelectionChangedListener(ISelectionChangedListener listener) {
      if (listener != null) {
         selectionChangedListeners.add(listener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeSelectionChangedListener(ISelectionChangedListener listener) {
      if (listener != null) {
         selectionChangedListeners.remove(listener);
      }
   }
   
   /**
    * Returns all registered {@link ISelectionChangedListener}s.
    * @return All registered {@link ISelectionChangedListener}s.
    */
   public ISelectionChangedListener[] getSelectionChangedListeners() {
      return selectionChangedListeners.toArray(new ISelectionChangedListener[selectionChangedListeners.size()]);
   }
   
   /**
    * Fires a selection changed event.
    * @param selection the new selection
    */
   protected void fireSelectionChanged(ISelection selection) {
       // create an event
       final SelectionChangedEvent event = new SelectionChangedEvent(this, selection);
       // fire the event
       ISelectionChangedListener[] listeners = getSelectionChangedListeners();
       for (final ISelectionChangedListener l : listeners) {
           SafeRunner.run(new SafeRunnable() {
               public void run() {
                   l.selectionChanged(event);
               }
           });
       }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Control getControl() {
      return root;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      if (treeViewer != null) {
         treeViewer.getControl().setFocus();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void openSearchPanel() {
      if (searchComposite == null || searchComposite.isDisposed()) {
         searchComposite = new SearchComposite(root, SWT.NONE, this);
         updateEmptySearchResult();
         searchComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         root.layout();
      }
      searchComposite.setFocus();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void closeSearchPanel() {
      disposeSearch();
      if (searchComposite != null) {
         searchComposite.dispose();
         searchComposite = null;
      }
      root.layout();
      treeViewer.refresh();
   }

   /**
    * Disposes the current search.
    */
   protected void disposeSearch() {
      if (searchJob != null) {
         searchJob.cancel();
         searchJob.dispose();
         searchJob = null;
         proofTreeColorManager.setSearch(null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void searchText(String text) {
      disposeSearch();
      if (!StringUtil.isEmpty(text)) {
         ISearchCallback callback = new ISearchCallback() {
            @Override
            public void searchCompleted(AbstractProofNodeSearch search) {
               if (search.isSearchComplete()) {
                  proofTreeColorManager.setSearch(searchJob);
               }
               else {
                  proofTreeColorManager.setSearch(null);
               }
               refreshTreeViewerAndUpdateSearchResultThreadSave();
            }
         };
         searchJob = new ProofNodeTextSearch(callback, this, labelProvider, proof, text);
         searchJob.schedule();
      }
      else {
         treeViewer.refresh();
         updateEmptySearchResult();
      }
   }

   /**
    * Refreshes {@link #treeViewer} and calls {@link #updateEmptySearchResult()} thread save.
    */
   protected void refreshTreeViewerAndUpdateSearchResultThreadSave() {
      treeViewer.getTree().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            if (!treeViewer.getTree().isDisposed()) {
               updateEmptySearchResult();
               treeViewer.refresh();
            }
         }
      });
   }

   /**
    * Updates the empty search flag of {@link #searchComposite}.
    */
   protected void updateEmptySearchResult() {
      searchComposite.setEmptySearchResult(searchJob == null || searchJob.isResultEmpty() || !searchJob.isSearchComplete());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void jumpToPreviousResult() {
      if (searchJob != null) {
         Node previous = searchJob.getPreviousResult(getSelectedNodeThreadSave());
         if (previous != null) {
            setSelectionThreadSave(SWTUtil.createSelection(previous));
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void jumpToNextResult() {
      if (searchJob != null) {
         Node next = searchJob.getNextResult(getSelectedNodeThreadSave());
         if (next != null) {
            setSelectionThreadSave(SWTUtil.createSelection(next));
         }
      }
   }
   
   /**
    * Calls {@link #getSelectedNode()} thread save.
    * @return The currently selected {@link Node} or {@code null} if not available.
    */
   protected Node getSelectedNodeThreadSave() {
      IRunnableWithResult<Node> run = new AbstractRunnableWithResult<Node>() {
         @Override
         public void run() {
            setResult(getSelectedNode());
         }
      };
      treeViewer.getTree().getDisplay().syncExec(run);
      return run.getResult();
   }

   /**
    * Calls {@link #setSelection(ISelection)} thread save.
    * @param selection The {@link ISelection} to set.
    */
   protected void setSelectionThreadSave(final IStructuredSelection selection) {
      if (!treeViewer.getTree().isDisposed()) {
         treeViewer.getTree().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!treeViewer.getTree().isDisposed()) {
                  setSelection(selection);
               }
            }
         });
      }
   }
}