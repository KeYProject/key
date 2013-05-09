package org.key_project.keyide.ui.editor;


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.SaveAsDialog;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.keyide.ui.editor.input.ProofEditorInput;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.util.LogUtil;
import org.key_project.keyide.ui.views.ProofTreeContentOutlinePage;
import org.key_project.keyide.ui.views.StrategyPropertiesView;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
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
  
   private boolean dirtyFlag = false;
      
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   private Proof proof;
      
   public ProofSourceViewerDecorator getTextViewer() {
      return textViewer;
   }
   
   private void setDirtyFlag(boolean dirtyFlag){
      this.dirtyFlag = dirtyFlag;
      Display display = Display.getDefault();
      display.asyncExec(new Runnable() {
         
         @Override
         public void run() {
            firePropertyChange(PROP_DIRTY);
            
         }
      });
   }

   
   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
      
      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofPruned(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofExpanded(ProofTreeEvent e) {
         handleProofChanged(e);
      }
      
      @Override
      public void proofClosed(ProofTreeEvent e) {
         handleProofChanged(e);
      }
   };
   
   
   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         if (showNode.getAppliedRuleApp() == null){
            textViewer.setBackgroundColorForHover();
         }
      }
   };
   
   
   @Override
   protected void doSetInput(IEditorInput input) throws CoreException {
      try {
         super.doSetInput(input);
         if (input instanceof ProofEditorInput) {
            ProofEditorInput in = (ProofEditorInput) input;
            this.proof = in.getProof();
            this.environment = in.getEnvironment();
            // TODO: Environment updaten.
         }
         else if (input instanceof FileEditorInput) {
            FileEditorInput fileInput = (FileEditorInput) input;
            File file = ResourceUtil.getLocation(fileInput.getFile());
            Assert.isTrue(file != null, "File \"" + fileInput.getFile() + "\" is not local.");
            // TODO: After save as the editor should be restored when eclipse is
            // reopened.
            Assert.isTrue(this.environment == null, "Environment already exist.");
            this.environment = KeYEnvironment.load(file, null, null);
            this.environment.getMediator().setStupidMode(true);
            Assert.isTrue(getKeYEnvironment().getLoadedProof() != null, "No proof loaded.");
            this.proof = getKeYEnvironment().getLoadedProof();
         }
      }
      catch (Exception e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   
   
   protected void handleProofChanged(ProofTreeEvent e) {
      setDirtyFlag(true);
   }


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
      dialog.setTitle("Save Proof");
      
      IEditorInput input = getEditorInput();
      if(input instanceof ProofEditorInput){
         IMethod method = ((ProofEditorInput)input).getMethod();
         IPath methodPath = method.getPath();
         methodPath = methodPath.removeLastSegments(1);
         String name = getProof().name().toString();
         name = makePathValid(name);
         name = name + ".proof";
         methodPath = methodPath.append(name);
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(methodPath);
         dialog.setOriginalFile(file);
      }
      else if(input instanceof FileEditorInput){
         FileEditorInput in = (FileEditorInput) input;
         IFile file = in.getFile();
         dialog.setOriginalFile(file);
      }
      dialog.create();
      dialog.open();
      // TODO: Funktionalität nutzen um dateiendung zu definieren
      // TODO: Container = IMethod's container
      // TODO: Name = Name des beweises
      

            
      
      IPath path = dialog.getResult();
      save(path);
   }
   
   
   private String makePathValid(String str){
      String tmp;
      for(int i = 1; i<=str.length();i++){
         tmp = str.substring(0, i);
         Path path = new Path(tmp);
         if(!path.isValidSegment(tmp)){
            StringBuilder strbuilder = new StringBuilder(str);
            strbuilder.setCharAt(i-1, '_');
            str = strbuilder.toString();
         }
      }
      return str;
   }
   

   @Override
   public void doSave(IProgressMonitor progressMonitor) {
      if(getEditorInput() instanceof FileEditorInput){
         FileEditorInput input = (FileEditorInput) getEditorInput();
         save(input.getFile().getFullPath());
      }
      else{
         doSaveAs();
      }
      
      //         IPath path = new Path(savedFile.getPath());
//         save(path);
//      }
   }

   
   private void save(IPath path){
      if(path != null){         
         IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
         String name = file.getLocation().toOSString();
         // Create proof file content
         // TODO: Refactor functionality to save a Proof into an IFile into a static utility method of KeYUtil#saveProof(Proof proof, IFile) and use this method also in SaveProofHandler
         ProofSaver saver = new ProofSaver(showNode.proof(), name, Main.INTERNAL_VERSION);
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         try {
            String errorMessage = saver.save(out);
            if (errorMessage != null) {
               throw new CoreException(LogUtil.getLogger().createErrorStatus(errorMessage));
            }
            // Save proof file content
            if (file.exists()) {
               file.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
            }
            else {
               file.create(new ByteArrayInputStream(out.toByteArray()), true, null);
            }
         }
         catch (IOException e){
            // TODO: Only one try catch in this method
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
         }
         catch (CoreException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
         }
         
         setDirtyFlag(false);   
      
         
         if(getEditorInput() instanceof ProofEditorInput){ // TODO: Always
            FileEditorInput fileInput = new FileEditorInput(file);
            try {
//               this.proof = ((ProofEditorInput)getEditorInput()).getProof();
//               this.environment = ((ProofEditorInput)getEditorInput()).getEnvironment();
               doSetInput(fileInput);
            }
            catch (CoreException e) {
               // TODO Auto-generated catch block
               e.printStackTrace();
            }
         }
      }
      
   }

   
   @Override
   public boolean isDirty(){
      return dirtyFlag;
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
      textViewer.setDocumentForNode(showNode, getKeYEnvironment().getMediator());
      if(showNode.getAppliedRuleApp() != null){
         PosInOccurrence posInOcc = showNode.getAppliedRuleApp().posInOccurrence();
         textViewer.setGreenBackground(posInOcc);
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
   public void createPartControl(Composite parent) {
      super.createPartControl(parent);
      getKeYEnvironment().getMediator().addKeYSelectionListener(keySelectionListener);
      getKeYEnvironment().getUi().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      ISourceViewer sourceViewer = getSourceViewer();
      textViewer = new ProofSourceViewerDecorator(sourceViewer);
      getProof().addProofTreeListener(proofTreeListener);
      sourceViewer.setEditable(false);
      sourceViewer.getTextWidget().addMouseMoveListener(mouseMoveListener);
      if (this.getShowNode() != null) {
         setShowNode(proof.root());
      }
      else {
         Node mediatorNode = environment.getMediator().getSelectedNode();
         setShowNode(mediatorNode != null ? mediatorNode : getProof().root());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEditable() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getKeYEnvironment().getUi().removePropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      getKeYEnvironment().getMediator().removeKeYSelectionListener(keySelectionListener);
      getProof().removeProofTreeListener(proofTreeListener);
      if (outline != null) {
         outline.dispose();         
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<CustomConsoleUserInterface> getKeYEnvironment() {
      return environment;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getProof() {
      return proof;
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
            }
         }
         return outline;
      }
      else if(StrategyPropertiesView.class.equals(adapter)){
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
