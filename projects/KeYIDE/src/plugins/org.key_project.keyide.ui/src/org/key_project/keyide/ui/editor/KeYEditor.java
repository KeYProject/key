package org.key_project.keyide.ui.editor;


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.keyide.ui.editor.input.ProofEditorInput;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.views.ProofTreeContentOutlinePage;
import org.key_project.keyide.ui.views.StrategyPropertiesView;

import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
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
   
   private ProofTreeContentOutlinePage outline;
   
   private Node showNode; 
   
   private ProofSourceViewerDecorator textViewer;
  
   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         textViewer.setBackgroundColorForHover();
      }
   };

   
   private KeYSelectionListener keySelectionListener = new KeYSelectionListener() {
      
      @Override
      public void selectedProofChanged(final KeYSelectionEvent e) {
         getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if(e.getSource().getSelectedNode() != null){
                  setShowNode(e.getSource().getSelectedNode());
               }
            }
         });
      }
      
      @Override
      public void selectedNodeChanged(final KeYSelectionEvent e) {
         getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if(e.getSource().getSelectedNode() != null){
                  setShowNode(e.getSource().getSelectedNode());
               }
            }
         });
      }
   };
   
   
   
   
   @Override
   public void doSaveAs() {
      // TODO Auto-generated method stub
      super.doSaveAs();
   }

   @Override
   public void doSave(IProgressMonitor progressMonitor) {
      // TODO Auto-generated method stub
      super.doSave(progressMonitor);
      //Overrride isDirty();
      firePropertyChange(PROP_DIRTY);
   }

   public Node getShowNode() {
      return showNode;
   }

   public void setShowNode(Node showNode) {
      this.showNode=showNode;
      textViewer.setDocumentForNode(getShowNode(), getKeYEnvironment().getMediator());
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
   public void createPartControl(Composite parent) {
      super.createPartControl(parent);
      getKeYEnvironment().getUi().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      ISourceViewer sourceViewer = getSourceViewer();
      textViewer = new ProofSourceViewerDecorator(sourceViewer);
      sourceViewer.setEditable(false);
      sourceViewer.getTextWidget().addMouseMoveListener(mouseMoveListener);
      if (this.getShowNode() != null) {
         textViewer.setDocumentForNode(getShowNode(), getKeYEnvironment().getMediator());
      }
      else {
         textViewer.setDocumentForNode(getProof().root(), getKeYEnvironment().getMediator());
      }
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getKeYEnvironment().getUi().removePropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      getKeYEnvironment().getMediator().removeKeYSelectionListener(keySelectionListener);
      outline.dispose();
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
               outline = new ProofTreeContentOutlinePage(getProof(), getKeYEnvironment());
               getKeYEnvironment().getMediator().addKeYSelectionListener(keySelectionListener);
            }
          
         }
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
