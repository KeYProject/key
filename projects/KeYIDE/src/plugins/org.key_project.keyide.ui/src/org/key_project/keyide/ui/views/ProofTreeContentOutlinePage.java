package org.key_project.keyide.ui.views;

import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.keyide.ui.util.TreeViewerIterator;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * A class to display the correct Outline for the current {@link Proof}
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofTreeContentOutlinePage extends ContentOutlinePage {
   private Proof proof;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   private KeYSelectionListener listener = new KeYSelectionListener() {
      @Override
      public void selectedProofChanged(KeYSelectionEvent e) {
         getTreeViewer().getControl().getDisplay().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               updateSelectedNode();
            }
         });
      }
      
      @Override
      public void selectedNodeChanged(KeYSelectionEvent e) {
         updateSelectedNode();
      }
   };
   
   private ISelectionChangedListener selectionChangedListener = new ISelectionChangedListener() {
      
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
      // TODO Auto-generated method stub
         
         Node node = getSelectedNode();
         if (environment.getMediator().getSelectionModel().getSelectedNode() != null){
            if (!environment.getMediator().getSelectionModel().getSelectedNode().equals(node)){
               environment.getMediator().getSelectionModel().setSelectedNode(node);
            }
         }
      }
   };
   
   /**
    * Constructor.
    * @param proof The {@link Proof} for this Outline.
    */
   public ProofTreeContentOutlinePage(Proof proof, KeYEnvironment<CustomConsoleUserInterface> environment) {
      this.proof = proof;
      this.environment = environment;
      environment.getMediator().getSelectionModel().addKeYSelectionListener(listener);
   }

   @Override
   public void dispose(){
      environment.getMediator().removeKeYSelectionListener(listener);
      getTreeViewer().removeSelectionChangedListener(selectionChangedListener);
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
      super.createControl(parent);
      getTreeViewer().setUseHashlookup(true);
      getTreeViewer().setContentProvider(new LazyProofTreeContentProvider(getTreeViewer(), environment, proof));
      getTreeViewer().setLabelProvider(new ProofTreeLabelProvider(getTreeViewer(), environment, proof));
      getTreeViewer().setInput(proof);
      getTreeViewer().addSelectionChangedListener(selectionChangedListener);
//      updateSelectedNode();
      
      MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
      Menu menu = menuManager.createContextMenu(getTreeViewer().getControl());
      getTreeViewer().getControl().setMenu(menu);
      getSite().registerContextMenu ("org.key_project.keyide.ui.view.outline.popup", menuManager, getTreeViewer());
   }

//   @Override
//   public void selectionChanged(SelectionChangedEvent event) {
//      Node node = getSelectedNode();
//      environment.getMediator().getSelectionModel().setSelectedNode(node);
//   }
   
   protected Node getSelectedNode() {
      Object selectedObj = SWTUtil.getFirstElement(getSelection());
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
   
   protected void updateSelectedNode() {
      Node mediatorNode = environment.getMediator().getSelectionModel().getSelectedNode();
      Object selectedNode = getSelectedNode();
      
      if (mediatorNode != selectedNode) {
         setSelection(SWTUtil.createSelection(mediatorNode));
      }
   }
   
}
