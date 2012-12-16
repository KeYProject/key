package org.key_project.keyide.ui.editor;


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.keyide.ui.editor.input.ProofEditorInput;
import org.key_project.keyide.ui.editor.input.ProofStorage;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.util.LogUtil;
import org.key_project.keyide.ui.views.Outline;
import org.key_project.keyide.ui.views.StrategyPropertiesView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.gui.nodeviews.NonGoalInfoView;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;



/**
 * This class represents the Editor for viewing KeY-Proofs
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYEditor extends TextEditor implements IProofEnvironmentProvider {
   public static final String EDITOR_ID = "org.key_project.keyide.ui.editor";
   
   private Outline outline;
   
   
   /**
    * Listener that changes the current EditorInput if the selection in the outline has changed.
    */
   private ISelectionChangedListener outlineSelectionListener = new ISelectionChangedListener() {
      // TODO change the input when the Node iteself changes. Example: OPEN GOAL becomes a proved Node
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         updateInput(event);
      }
   };
   
   private void updateInput(SelectionChangedEvent event){
      Node node = null;
      IEditorInput input = getEditorInput();
      if(input instanceof ProofEditorInput){
         //get the selected item
         ISelection selection = event.getSelection();
         if(selection instanceof TreeSelection){
            TreeSelection treeSelection = (TreeSelection) selection;
            if(!treeSelection.isEmpty()){
               if(treeSelection.getFirstElement() instanceof Node){
                  //get the Node
                  node = (Node) treeSelection.getFirstElement();
               }
               else if(treeSelection.getFirstElement() instanceof BranchFolder){
                  //get the BranchFolders ChildNode
                  BranchFolder branchFolder = (BranchFolder) treeSelection.getFirstElement();
                  node = branchFolder.getChild();
               }
            }
         }
         //SetUp the new EditorInput
         ((ProofEditorInput)input).setData(node);
         try {
            doSetInput(input);
         }
         catch (CoreException e) {
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   /**
    * Listens for changes on {@link ConsoleUserInterface#isAutoMode()} 
    * of the {@link ConsoleUserInterface} provided via {@link #getKeYEnvironment()}.
    */
   private PropertyChangeListener autoModeActiveListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         AutoModeTester.updateProperties();
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      super.init(site, input);
      getKeYEnvironment().getUi().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getKeYEnvironment().getUi().removePropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      outline.removeSelectionChangedListener(outlineSelectionListener);
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<CustomConsoleUserInterface> getKeYEnvironment() {
      Assert.isTrue(getEditorInput() instanceof ProofEditorInput);
      return ((ProofEditorInput)getEditorInput()).getEnvironment();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getProof() {
      Assert.isTrue(getEditorInput() instanceof ProofEditorInput);
      return ((ProofEditorInput)getEditorInput()).getProof();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IContentOutlinePage.class.equals(adapter)) {
         synchronized (this) {
            if (outline == null) {
               outline = new Outline(getProof(), getKeYEnvironment());
            }
          
         }
         //adds a ISelectionChangedListener to the Outline
         outline.addSelectionChangedListener(outlineSelectionListener);
         return outline;
      }
      if(StrategyPropertiesView.class.equals(adapter)){
         return getProof();
      }

      else if (IProofEnvironmentProvider.class.equals(adapter)) {
         return this;
      }
      else {
         return super.getAdapter(adapter);
      }
   } 
}
