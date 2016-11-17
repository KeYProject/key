package org.key_project.keyide.ui.composite;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
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

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

/**
 * This {@link Composite} shows the proof tree.
 * @author Martin Hentschel
 */
public class ProofTreeComposite extends Composite implements IProofNodeSearchSupport {
   /**
    * The {@link Proof} which provides the proof tree to show.
    */
   private Proof proof;
   
   /**
    * The used {@link ObservableTreeViewer} which shows the proof tree.
    */
   private ObservableTreeViewer treeViewer;

   /**
    * The by {@link #treeViewer} used {@link LazyProofTreeContentProvider}.
    */
   private LazyProofTreeContentProvider contentProvider;

   /**
    * The by {@link #treeViewer} used {@link ProofTreeLabelProvider}.
    */
   private ProofTreeLabelProvider labelProvider;
   
   /**
    * The used {@link ProofTreeColorManager}.
    */
   private ProofTreeColorManager proofTreeColorManager;
   
   /**
    * The {@link State} which indicates hiding or showing of intermediate proofsteps.
    */
   private State hideState;
   
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
    * The {@link State} for the show symbolic execution tree only outline filter.
    */
   private State symbolicState;
   
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
    * The used {@link SearchComposite}.
    */
   private SearchComposite searchComposite;
   
   /**
    * A search for proof nodes.
    */
   private ProofNodeTextSearch searchJob;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @param treeStyle The style for the {@link TreeViewer}.
    * @param proof The {@link Proof}.
    * @param environment The {@link KeYEnvironment} of the given {@link Proof}.
    */
   public ProofTreeComposite(Composite parent, int style, int treeStyle, Proof proof, KeYEnvironment<?> environment) {
      super(parent, style);
      this.proof = proof;
      // Hide and symbolic state
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
      setLayout(rootLayout);
      // Color Manager
      proofTreeColorManager = new ProofTreeColorManager(parent.getDisplay());
      proofTreeColorManager.addPropertyChangeListener(new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            handleProofTreeColorChanged();
         }
      });
      // Create TreeViewer
      treeViewer = new ObservableTreeViewer(this, treeStyle);
      treeViewer.getTree().setLayoutData(new GridData(GridData.FILL_BOTH));
      treeViewer.setUseHashlookup(true);
      treeViewer.addViewerUpdateListener(new IViewerUpdateListener() {
         @Override
         public void itemUpdated(ViewerUpdateEvent e) {
            handleItemUpdated(e);
         }
      });
      contentProvider = new LazyProofTreeContentProvider(environment != null ? environment.getProofControl() : null);
      // initialize boolean flags for hideIntermediateProofSteps and showSymbolicExecutionTree outline filter
      contentProvider.setHideState((boolean) hideState.getValue());
      contentProvider.setSymbolicState((boolean) symbolicState.getValue());
      treeViewer.setContentProvider(contentProvider);
      labelProvider = new ProofTreeLabelProvider(treeViewer, environment != null ? environment.getProofControl() : null, proof);
      treeViewer.setLabelProvider(labelProvider);
      treeViewer.setInput(proof);
      contentProvider.injectTopLevelElements();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      disposeSearch();
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      if (proofTreeColorManager != null) {
         proofTreeColorManager.dispose();
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
    * Changes the shown proof.
    * @param newProof The new {@link Proof}.
    * @param newEnvironment The new {@link SymbolicExecutionEnvironment}.
    */
   public void changeProof(Proof newProof, 
                           SymbolicExecutionEnvironment<?> newEnvironment) {
      this.proof = newProof;
      contentProvider.setProofControl(newEnvironment != null ? newEnvironment.getProofControl() : null);
      if (newProof != null) {
         treeViewer.setInput(newProof);
         if (labelProvider != null) {
            labelProvider.dispose();
         }
         labelProvider = new ProofTreeLabelProvider(treeViewer, newEnvironment.getProofControl(), newProof);
         treeViewer.setLabelProvider(labelProvider);
         contentProvider.injectTopLevelElements();
      }
      else {
         treeViewer.setInput(null);
      }
      closeSearchPanel();
   }

   /**
    * Returns the used {@link ObservableTreeViewer}.
    * @return The used {@link ObservableTreeViewer}.
    */
   public ObservableTreeViewer getTreeViewer() {
      return treeViewer;
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
    * Handles a change in the state of the showSymbolicExecutionTree outline filter.
    * @param state The state that has changed; never null. The value for this state has been updated to the new value.
    * @param oldValue The old value; may be anything.
    */
   protected void handleSymbolicStateChanged(State state, Object oldValue) {
      Node currentSelection = getSelectedNode();
      contentProvider.setSymbolicState((boolean) state.getValue());
      treeViewer.setInput(proof);
      if (currentSelection != null) {
         selectNodeThreadSafe(currentSelection);
      }
   }

   /**
    * Handles a change in the state of the hideIntermediateProofsteps outline filter.
    * @param state The state that has changed; never null. The value for this state has been updated to the new value.
    * @param oldValue The old value; may be anything.
    */
   protected void handleHideStateChanged(State state, Object oldValue) {
      Node currentSelection = getSelectedNode();
      contentProvider.setHideState((boolean) state.getValue());
      treeViewer.setInput(proof);
      if (currentSelection != null) {
         selectNodeThreadSafe(currentSelection);
      }
   }
   
   /**
    * Shows a new sub tree.
    * @param keepSelection {@code true} keep selection, {@code false} do not keep selection
    */
   public void showSubtree(boolean keepSelection, boolean showSubtree, Node baseNode) {
      if (proof != null && treeViewer != null) {
         Node currentSelection = getSelectedNode();
         if (showSubtree) {
            contentProvider.setShowSubtreeState(true, baseNode);
         }
         else {
            contentProvider.setShowSubtreeState(false, proof.root());
         }
         treeViewer.setInput(proof);
         if (currentSelection != null && keepSelection) {
            selectNodeThreadSafe(currentSelection);
         }
      }
   }
   
   /**
    * method to select a node thread safe.
    * @param node the {@link Node} to select
    */
   public void selectNodeThreadSafe(final Node node) {
      if (!treeViewer.getControl().getDisplay().isDisposed()) {
         treeViewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!treeViewer.getControl().isDisposed()) {
                  selectNode(node);
               }
            }
         });
      }
   }
   
   /**
    * Selects a given {@link Node}. 
    * @param node the {@link Node} to select
    */
   public void selectNode(Node nodeToSelect) {
      Node selectedNode = getSelectedNode();
      if (selectedNode != nodeToSelect) {
         // Make sure that Node to select is loaded in lazy TreeViewer
         makeSureElementIsLoaded(nodeToSelect);
         if (nodeToSelect != null) {
            Object parent = contentProvider.getParent(nodeToSelect);
            int viewIndex = contentProvider.getIndexOf(parent, nodeToSelect);
            // Select Node in lazy TreeViewer or the parent node when the node got filtered out
            if (viewIndex >= 0) {
               treeViewer.setSelection(SWTUtil.createSelection(nodeToSelect), true);
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
    * Makes sure that the given {@link Node} is known by the shown {@link TreeViewer}.
    * @param node The {@link Node} to make that is known by the shown {@link TreeViewer}.
    */
   public void makeSureElementIsLoaded(Node node) {
      makeSureElementIsLoaded(node, treeViewer, contentProvider);
   }

   /**
    * Makes sure that the given {@link Node} is known by the shown {@link TreeViewer}.
    * @param node The {@link Node} to make that is known by the shown {@link TreeViewer}.
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
   public void openSearchPanel() {
      if (searchComposite == null || searchComposite.isDisposed()) {
         searchComposite = new SearchComposite(this, SWT.NONE, this);
         updateEmptySearchResult();
         searchComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         layout();
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
      layout();
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
            selectNodeThreadSafe(previous);
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
            selectNodeThreadSafe(next);
         }
      }
   }
   
   /**
    * Calls {@link #getSelectedNode()} thread save.
    * @return The currently selected {@link Node} or {@code null} if not available.
    */
   public Node getSelectedNodeThreadSave() {
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
    * Returns the selected {@link Node}.
    * @return The selected {@link Node} or {@code null} if no {@link Node} is selected.
    */
   public Node getSelectedNode() {
      return getSelectedNode(getSelection());
   }
   
   /**
    * Returns the current {@link ISelection} of {@link #getTreeViewer()}.
    * @return The current {@link ISelection} of {@link #getTreeViewer()}.
    */
   public ISelection getSelection() {
      return treeViewer.getSelection();
   }

   /**
    * Returns the selected {@link Node} provided by the given {@link ISelection}.
    * @param selection The {@link ISelection} to extract selected {@link Node} from.
    * @return The selected {@link Node} or {@code null} if no {@link Node} is selected.
    */
   public static Node getSelectedNode(ISelection selection) {
      Object selectedObj = SWTUtil.getFirstElement(selection);
      if (selectedObj instanceof Node) {
         return (Node) selectedObj;
      }
      else if (selectedObj instanceof BranchFolder) {
         return ((BranchFolder) selectedObj).getChild();
      }
      else {
         return null;
      }
   }
}
