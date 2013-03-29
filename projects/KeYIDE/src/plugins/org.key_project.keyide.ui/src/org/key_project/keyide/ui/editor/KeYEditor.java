package org.key_project.keyide.ui.editor;


import java.awt.Menu;
import java.awt.MenuItem;
import java.awt.Point;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.SaveAsDialog;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.keyide.ui.editor.input.ProofEditorInput;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.views.ProofTreeContentOutlinePage;
import org.key_project.keyide.ui.views.StrategyPropertiesView;

import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
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
  
   public ProofSourceViewerDecorator getTextViewer() {
      return textViewer;
   }

   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         if (showNode.getAppliedRuleApp() == null){
            textViewer.setBackgroundColorForHover();
         }
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
                  if(showNode.getAppliedRuleApp() != null){
                     PosInOccurrence posInOcc = showNode.getAppliedRuleApp().posInOccurrence();
                     PosInSequent pos = PosInSequent.createCfmaPos(posInOcc);
                     textViewer.setGreenBackground(posInOcc);
                  }
               }
            }
         });
      }
   };
   
   
   /**
    * Constructor to initialize the ContextMenu IDs
    */
   public KeYEditor() {
      setEditorContextMenuId("#KeYEditorContext");
      setRulerContextMenuId("#KeYEditorRulerContext");
   }
   
   /**
    * Saves the current {@link Proof} as a .proof file.
    */
   @Override
   public void doSaveAs() {
      Shell shell = getSite().getWorkbenchWindow().getShell();
      SaveAsDialog dialog = new SaveAsDialog(shell);
      dialog.create();
      dialog.setTitle("Save Proof");
      dialog.open();
      
      IPath path = dialog.getResult();
      if(path != null){
         final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
         String fileExtension = KeYUtil.PROOF_FILE_EXTENSION;
         String fileName = file.getLocation().toString();
         if(!fileName.endsWith(".proof")){
            fileName = fileName + "." + fileExtension;
         }
         ProofSaver saver = new ProofSaver(showNode.proof(), fileName, null);
         
         try {
            saver.save();
         }
         catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
      }
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

   
   /**
    * Sets the showNode and the {@link Document} for the {@link ISourceViewer} of the {@link ProofSourceViewerDecorator}.
    * @param showNode the new shown {@link Node}.
    */
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
         setShowNode(getProof().root());
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
