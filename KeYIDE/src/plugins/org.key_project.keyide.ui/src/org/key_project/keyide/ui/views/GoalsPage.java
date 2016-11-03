package org.key_project.keyide.ui.views;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.Page;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.GoalsLabelProvider;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.core.KeYSelectionModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

/**
 * The {@link IGoalsPage} which is returned by the active {@link KeYEditor}. The
 * aim of this {@link IGoalsPage} is to show all open {@link Goal}s by using a
 * {link TableViewer}.
 * 
 * @author Seena Vellaramkalayil
 */
public class GoalsPage extends Page implements IGoalsPage {
   /**
    * the currently loaded proof.
    */
   private Proof proof;

   /**
    * the viewer of this page.
    */
   private TableViewer viewer;
   
   /**
    * the environment of the proof.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * the selection model.
    */
   private KeYSelectionModel selectionModel;
   
   /**
    * the content provider for the viewer.
    */
   private ImmutableCollectionContentProvider contentProvider;
   
   /**
    * the label provider for the viewer.
    */
   private GoalsLabelProvider labelProvider;

   /**
    * The {link KeySelectionListener} listens to changes on the current
    * {@link KeYSelectionModel}.
    */
   private KeYSelectionListener keySelectionListener = new KeYSelectionListener() {
      @Override
      public void selectedNodeChanged(KeYSelectionEvent e) {
         handleSelectedNodeChanged(e);
      }

      @Override
      public void selectedProofChanged(KeYSelectionEvent e) {
         handleSelectedProofChanged(e);
      }
   };

   /**
    * The {@link ProofTreeListener} listens to any changes that are made on the
    * current {@link Proof}.
    */
   private ProofTreeListener proofTreeListener = new ProofTreeAdapter() {
      @Override
      public void proofClosed(ProofTreeEvent e) {
         updateGoalsThreadSafe();
      }

      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         updateGoalsThreadSafe();
      }

      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         updateGoalsThreadSafe();
      }

      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
         updateGoalsThreadSafe();
      }
   };

   /**
    * The {@link AutoModeListener} listens to starting and stopping the auto
    * mode.
    */
   private final AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted();
      }

      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
   };

   /**
    * The {@link ISelectionListener} listens to selection changes that are made
    * on any other views. If a change is made on the {@link GoalsView}, the
    * selectionModel has to be updated.
    */
   private final ISelectionListener selectionListener = new ISelectionListener() {
      @Override
      public void selectionChanged(IWorkbenchPart part, ISelection selection) {
         if (selection instanceof IStructuredSelection && part instanceof GoalsView) {
            Object selectedObj = SWTUtil.getFirstElement(selection);
            if (selectedObj instanceof Goal) {
               selectionModel.setSelectedGoal((Goal) selectedObj);
            }
         }
      }
   };

   /**
    * Constructor.
    * 
    * @param proof
    *           The current {@link Proof} for receiving the goals.
    * @param environment
    *           The {@link KeYEnvironment} to add the autoModeListener to.
    * @param selectionModel
    *           The {@link KeYSelectionModel} to add the keySelectionListener
    *           to.
    */
   public GoalsPage(Proof proof, KeYEnvironment<?> environment, KeYSelectionModel selectionModel) {
      this.proof = proof;
      this.environment = environment;
      this.selectionModel = selectionModel;
      this.proof.addProofTreeListener(proofTreeListener);
      this.environment.getProofControl().addAutoModeListener(autoModeListener);
      this.selectionModel.addKeYSelectionListener(keySelectionListener);
   }

   /**
    * Method handles selection changes on the proof.
    * @param e 
    */
   protected void handleSelectedProofChanged(KeYSelectionEvent e) {
      if (e.getSource().getSelectedNode().proof() == proof) {
         updateSelectionThreadSafe();
      }
   }
   
   /**
    * Method handles selection changes on a node.
    * @param e
    */
   protected void handleSelectedNodeChanged(KeYSelectionEvent e) {
      updateSelectionThreadSafe();
   }
   
   /**
    * Method handles the page when the auto mode stops.
    * @param e
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (e.getSource() == proof) {
         proof.addProofTreeListener(proofTreeListener);
         updateGoalsThreadSafe();
      }
   }
   
   /**
    * Method handles the page when the auto mode starts.
    */
   protected void handleAutoModeStarted() {
      proof.removeProofTreeListener(proofTreeListener);
   }

   /**
    * Method executes {@link #handleGoalsChanged()} asynchronously and thread safe.
    */
   protected void updateGoalsThreadSafe() {
      if (!viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  handleGoalsChanged();
               }
            }
         });
      }
   }
   
   /**
    * This method sets a new input to the viewer and is called when the proof 
    * has changed.
    */
   protected void handleGoalsChanged() {
      ImmutableList<Goal> goals = proof.openGoals();
      if (!ObjectUtil.equals(goals, viewer.getInput())) {
         labelProvider.dispose();
         labelProvider = new GoalsLabelProvider(viewer, goals);
         viewer.setLabelProvider(labelProvider);
         viewer.setInput(goals);
      }
   }
   
   /**
    * Method updates the selection of the viewer when there are changes.
    */
   protected void updateSelectedNode() {
      Node mediatorNode = selectionModel.getSelectedNode();
      Object selectedNode = getSelectedNode(viewer.getSelection());
      if (mediatorNode != selectedNode) {
         viewer.setSelection(SWTUtil.createSelection(proof.getGoal(mediatorNode)), true);
      }
   }
   
   /**
    * Method returns the selected {@link Node}.
    * @param selection the current seletion
    * @return The selected {@link Node} or {@code null} if no {@link Node} is selected.
    */
   protected Node getSelectedNode(ISelection selection) {
      Object selectedObj = SWTUtil.getFirstElement(selection);
      if (selectedObj instanceof Node) {
         return (Node) selectedObj;
      }
      else if (selectedObj instanceof BranchFolder) {
         return ((BranchFolder) selectedObj).getChild();
      }
      else if (selectedObj instanceof Goal) {
         return ((Goal) selectedObj).node();
      }
      else {
         return null;
      }
   }
   
   /**
    * Executes {@link #updateSelectedNode()} asynchronously and thread safe.
    */
   protected void updateSelectionThreadSafe() {
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
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      viewer = new TableViewer(parent);
      contentProvider = new ImmutableCollectionContentProvider();
      ImmutableList<Goal> goals = proof.openGoals();
      labelProvider = new GoalsLabelProvider(viewer, goals);
      viewer.setContentProvider(contentProvider);
      viewer.setLabelProvider(labelProvider);
      viewer.setInput(goals);
      getSite().setSelectionProvider(viewer); //allow listening to selection changes of this viewer
      getSite().getPage().addSelectionListener(selectionListener);
      updateSelectedNode();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Control getControl() {
      return viewer.getControl();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      if (viewer.getControl() != null && !viewer.getControl().isDisposed()) {
         viewer.getControl().setFocus();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (viewer.getControl() != null) {
         viewer.getControl().dispose();
      }
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      environment.getProofControl().removeAutoModeListener(autoModeListener);
      proof.removeProofTreeListener(proofTreeListener);
      selectionModel.removeKeYSelectionListener(keySelectionListener);
      getSite().getPage().removeSelectionListener(selectionListener);
      super.dispose();
   }
}
