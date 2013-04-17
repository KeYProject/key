package org.key_project.keyide.ui.views;

import java.util.Deque;
import java.util.LinkedList;

import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * A class to display the correct Outline for the current {@link Proof}
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan K�sdorf, Marco Drebing
 */
public class ProofTreeContentOutlinePage extends ContentOutlinePage {
   // TODO: Document members of ProofTreeContentOutlinePage
   private Proof proof;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;

   private LazyProofTreeContentProvider contentProvider;
   
   private ProofTreeLabelProvider labelProvider;
   
   /**
    * {@link KeYSelectionListener} to sync the KeYSelection with the treeselection.
    */
   private KeYSelectionListener listener = new KeYSelectionListener() {
      @Override
      public void selectedProofChanged(KeYSelectionEvent e) {
         updateSelectedNodeThreadSafe();
      }
      
      @Override
      public void selectedNodeChanged(KeYSelectionEvent e) {
         updateSelectedNodeThreadSafe();
      }
   };
   
   private AutoModeListener autoModeListener = new AutoModeListener() {
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
    * Constructor.
    * @param proof The {@link Proof} for this Outline.
    */
   public ProofTreeContentOutlinePage(Proof proof, KeYEnvironment<CustomConsoleUserInterface> environment) {
      this.proof = proof;
      this.environment = environment;
      environment.getMediator().addKeYSelectionListener(listener);
      environment.getMediator().addAutoModeListener(autoModeListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose(){
      environment.getMediator().removeKeYSelectionListener(listener);
      environment.getMediator().removeAutoModeListener(autoModeListener);
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();
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
      contentProvider = new LazyProofTreeContentProvider(getTreeViewer(), environment, proof);
      getTreeViewer().setContentProvider(contentProvider);
      labelProvider = new ProofTreeLabelProvider(getTreeViewer(), environment, proof);
      getTreeViewer().setLabelProvider(labelProvider);
      getTreeViewer().setInput(proof);
      // Create context menu of TreeViewer
      MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
      Menu menu = menuManager.createContextMenu(getTreeViewer().getControl());
      getTreeViewer().getControl().setMenu(menu);
      getSite().registerContextMenu ("org.key_project.keyide.ui.view.outline.popup", menuManager, getTreeViewer());
   }

   /**
    * When the auto mode starts.
    * @param e The event.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      // Ignore mediator selection changes while auto mode is running (Behavior of original KeY UI and solves problem with selection synchronization with the shown TreeViewer)
      environment.getMediator().removeKeYSelectionListener(listener);
   }

   /**
    * When the auto mode stops.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      // Listen for mediator selection changes caused by the user to synchronize them with the shown TreeViewer 
      environment.getMediator().addKeYSelectionListener(listener);
      // Make sure that correct selected node is shown
      updateSelectedNodeThreadSafe();
   }
   
   /**
    * Executes {@link #updateSelectedNode()} asynchronously and thread safe.
    */
   protected void updateSelectedNodeThreadSafe() {
      getControl().getDisplay().asyncExec(new Runnable() {
         @Override
         public void run() {
            updateSelectedNode();
         }
      });
   }
   
   /**
    * Updates the selected node of the shown {@link TreeViewer} 
    * when the selection of the {@link KeYMediator} has changed.
    */
   protected void updateSelectedNode() {
      Node mediatorNode = environment.getMediator().getSelectedNode();
      Object selectedNode = getSelectedNode();
      if (mediatorNode != selectedNode) {
         // Make sure that Node to select is loaded in lazy TreeViewer
         makeSureElementIsLoaded(mediatorNode);
         // Select Node in lazy TreeViewer
         setSelection(SWTUtil.createSelection(mediatorNode));
      }
   }

   /**
    * Makes sure that the given {@link Node} is known by the shown {@link TreeViewer}.
    * @param node The {@link Node} to make that is known by the shown {@link TreeViewer}.
    */
   protected void makeSureElementIsLoaded(Node node) {
      // Collect unknown parents
      Deque<Object> unknownParents = new LinkedList<Object>();
      boolean unknown = true;
      Object current = node;
      while (unknown && current != null) {
         if (getTreeViewer().testFindItem(current) == null) {
            unknownParents.addFirst(current);
         }
         else {
            unknown = false;
         }
         current = contentProvider.getParent(current);
      }
      // Inject unknown elements
      for (Object unknownElement : unknownParents) {
         Object parent = contentProvider.getParent(unknownElement);
         int viewIndex = contentProvider.getIndexOf(parent, unknownElement);
         contentProvider.updateChildCount(parent, 0);
         contentProvider.updateElement(parent, viewIndex);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void selectionChanged(SelectionChangedEvent event) {
      // Change selected node of mediator only if content provider is not in refresh phase after stopping the auto mode
      if (!contentProvider.isRefreshAfterAutoModeStopped()) {
         Node node = getSelectedNode(event.getSelection());
         Node mediatorNode = environment.getMediator().getSelectedNode();
         if (node != mediatorNode) {
            environment.getMediator().getSelectionModel().setSelectedNode(node);
         }
      }
      // Fire event to listener
      super.selectionChanged(event); 
   }
   
   /**
    * Returns the selected {@link Node}.
    * @return The selected {@link Node} or {@code null} if no {@link Node} is selected.
    */
   protected Node getSelectedNode() {
      return getSelectedNode(getSelection());  
   }

   /**
    * Returns the selected {@link Node} provided by the given {@link ISelection}.
    * @param selection The {@link ISelection} to extract selected {@link Node} from.
    * @return The selected {@link Node} or {@code null} if no {@link Node} is selected.
    */
   protected Node getSelectedNode(ISelection selection) {
      Object selectedObj = SWTUtil.getFirstElement(selection);
      if (selectedObj instanceof Node) {
         return (Node)selectedObj;
      }
      else if (selectedObj instanceof BranchFolder) {
         return ((BranchFolder)selectedObj).getChild();
      }
      else {
         return null;
      }
   }
}
