/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.keyide.ui.editor;


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.keyide.ui.editor.input.ProofEditorInput;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.util.LogUtil;
import org.key_project.keyide.ui.views.ProofTreeContentOutlinePage;

import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;



/**
 * This class represents the Editor for viewing KeY-Proofs
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYEditor extends TextEditor implements IProofProvider {
   public static final String EDITOR_ID = "org.key_project.keyide.ui.editor";
   
   private ProofTreeContentOutlinePage outline;
   
   private Node showNode; 
   
   private ProofSourceViewerDecorator textViewer; // TODO: Rename, into proofDecorator. And also its getter
   
   /**
    * Contains the registered {@link IProofProviderListener}.
    */
   private List<IProofProviderListener> proofProviderListener = new LinkedList<IProofProviderListener>();
  
//   private boolean dirtyFlag = false;
   
//   private File savedFile;
   
   public ProofSourceViewerDecorator getTextViewer() { // TODO Change order: attributes, constructors, methods, getter/setters (linke in UML) 
      return textViewer;
   }

//   private void setDirtyFlag(boolean dirtyFlag){
//      this.dirtyFlag = dirtyFlag;
//      firePropertyChange(PROP_DIRTY);
//   }

   
//   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
//      
//      @Override
//      public void smtDataUpdate(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofStructureChanged(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofPruned(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofIsBeingPruned(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofGoalsChanged(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofGoalsAdded(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofGoalRemoved(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofExpanded(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//      
//      @Override
//      public void proofClosed(ProofTreeEvent e) {
//         handleProofChanged(e);
//      }
//   };
   
   
   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         // TODO: Refactor functionality into KeYEditor#handleMouseMoved(MouseEvent) which is called here
         if (showNode.getAppliedRuleApp() == null){
            textViewer.setBackgroundColorForHover();
         }
      }
   };
   
   
   @Override
   protected void doSetInput(IEditorInput input) throws CoreException {
      if(input instanceof ProofEditorInput){
         super.doSetInput(input);
      }
      else {
         throw new CoreException(LogUtil.getLogger().createErrorStatus("Unsupported editor input: " + input));
      }
//      else if(input instanceof FileEditorInput){
//         FileEditorInput fileInput = (FileEditorInput) input;
////         System.out.println(fileInput.getFile().getFullPath());
//         final File file = fileInput.getFile().getFullPath().toFile();
//         savedFile = file;
//         KeYFile keyFile = new KeYFile(null, file, null);
//         try {
//            String javaPath = keyFile.readJavaPath();
//         }
//         catch (ProofInputException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//         }
//         final File boot = keyFile.readBootClassPath();
//         final List<File> classPaths = keyFile.readClassPath();
//         try {
//            final KeYEnvironment<CustomConsoleUserInterface> environment = KeYEnvironment.load(file, classPaths, boot);
//            Proof proof = environment.getLoadedProof();
//            environment.getMediator().setStupidMode(true);
//            String inputText = NonGoalInfoView.computeText(environment.getMediator(), proof.root());
//            IStorage storage = new ProofStorage(inputText, proof.name().toString());
//            IStorageEditorInput storageEditorInput = new ProofEditorInput(storage, proof, environment);
//            super.doSetInput(storageEditorInput);
//}
//         catch (ProblemLoaderException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//         }
//      }
      
   }
   
   
//   protected void handleProofChanged(ProofTreeEvent e) {
//      setDirtyFlag(true);
//   }


   private KeYSelectionListener keySelectionListener = new KeYSelectionListener() {
      
      @Override
      public void selectedProofChanged(final KeYSelectionEvent e) {
         // TODO: Refactor functionality into KeYEditor#handleSelectedProofChanged(KeYSelectionEvent) which is called here
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
         // TODO: Refactor functionality into KeYEditor#handleSelectedNodeChanged(KeYSelectionEvent) which is called here
         getEditorSite().getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if(e.getSource().getSelectedNode() != null){
                  setShowNode(e.getSource().getSelectedNode());
                  if(showNode.getAppliedRuleApp() != null){
                     PosInOccurrence posInOcc = showNode.getAppliedRuleApp().posInOccurrence();
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
      Shell shell = getSite().getShell();
      MessageDialog.openInformation(shell, "Information", "Save As is currently not supported.");
//      SaveAsDialog dialog = new SaveAsDialog(shell);
//      dialog.create();
//      dialog.setTitle("Save Proof");
//      dialog.open();
//      // TODO: Funktionalität nutzen um dateiendung zu definieren
//      // TOOD: Container = IMethod's container
//      // TODO: Name = Name des beweises
//
//            
//      
//      IPath path = dialog.getResult();
//      save(path);
   }
   
   

   @Override
   public void doSave(IProgressMonitor progressMonitor) {
//      if(savedFile == null){
//         doSaveAs();
//      }
//      else{
//         IPath path = new Path(savedFile.getPath());
//         save(path);
//      }
   }

   
//   private void save(IPath path){
//      if(path != null){
//         
//         IWorkspaceRoot workSpaceRoot = ResourcesPlugin.getWorkspace().getRoot();
//         final IFile file = workSpaceRoot.getFile(path);
//         IProject project = file.getProject();
//         File rawPath = ResourceUtil.getLocation(file);
//         
////         String fileExtension = KeYUtil.PROOF_FILE_EXTENSION;
////         if(!rawPath.endsWith(".proof")){
////            rawPath = rawPath + "." + fileExtension;
////         } /// TODO : Should be done in UI
//         ProofSaver saver = new ProofSaver(showNode.proof(), rawPath.getAbsolutePath(), null);
//         // TODO: Similar to SaveProofHandler line 73 ...
//         try {
//            saver.save();
//            project.refreshLocal(IResource.DEPTH_INFINITE, null);
//            savedFile = file.getFullPath().toFile();
//         }
//         catch (IOException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//         }
//         catch (CoreException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//         }
//         
//      }
//      setDirtyFlag(false);
//   }
//
//   
//   @Override
//   public boolean isDirty(){
//      return dirtyFlag;
//   }
   

   
   public Node getShowNode() { // TODO: Document method getShowNode()
      return showNode;
   }

   
   /**
    * Sets the showNode and the {@link Document} for the {@link ISourceViewer} of the {@link ProofSourceViewerDecorator}.
    * @param showNode the new shown {@link Node}.
    */
   public void setShowNode(Node showNode) {
      this.showNode=showNode;
      textViewer.setDocumentForNode(getShowNode(), getEnvironment().getMediator());
   }
   
   
   /**
    * Listens for changes on {@link ConsoleUserInterface#isAutoMode()} 
    * of the {@link ConsoleUserInterface} provided via {@link #getEnvironment()}.
    */
   private PropertyChangeListener autoModeActiveListener = new PropertyChangeListener() { // TODO: Move to the top of the class, order is attributes, constructors, methods like in UML
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         AutoModeTester.updateProperties();
      }
   };
   
   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
      }
      
      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
      }
      
      @Override
      public void proofPruned(ProofTreeEvent e) {
      }
      
      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
      }
      
      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
      }
      
      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
      }
      
      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
      }
      
      @Override
      public void proofExpanded(ProofTreeEvent e) {
      }
      
      @Override
      public void proofClosed(ProofTreeEvent e) {
         handleProofClosed(e);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      super.init(site, input);
      getCurrentProof().addProofTreeListener(proofTreeListener);
      getEnvironment().getUi().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
   }


   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      super.createPartControl(parent);
      getEnvironment().getUi().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      ISourceViewer sourceViewer = getSourceViewer();
      textViewer = new ProofSourceViewerDecorator(sourceViewer);
//      getProof().addProofTreeListener(proofTreeListener); // Is this line irrelevant? Remove it from source code!
      sourceViewer.setEditable(false);
      sourceViewer.getTextWidget().addMouseMoveListener(mouseMoveListener);
      if (this.getShowNode() != null) {
         textViewer.setDocumentForNode(getShowNode(), getEnvironment().getMediator());
      }
      else {
         setShowNode(getCurrentProof().root());
      }
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getCurrentProof().removeProofTreeListener(proofTreeListener);
      getEnvironment().getUi().removePropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      getEnvironment().getMediator().removeKeYSelectionListener(keySelectionListener);
      outline.dispose();
      if (outline != null) {
         outline.dispose();
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
      Assert.isTrue(getEditorInput() instanceof ProofEditorInput);
      return ((ProofEditorInput)getEditorInput()).getEnvironment();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getCurrentProof() {
      Assert.isTrue(getEditorInput() instanceof ProofEditorInput);
      return ((ProofEditorInput)getEditorInput()).getProof();
   }


   @Override
   public Proof[] getCurrentProofs() {
      Proof proof = getCurrentProof();
      return proof != null ? new Proof[] {proof} : new Proof[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public UserInterface getUI() {
      KeYEnvironment<?> environment = getEnvironment();
      return environment != null ? environment.getUi() : null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IContentOutlinePage.class.equals(adapter)) {
         synchronized (this) {
            if (outline == null) {
               outline = new ProofTreeContentOutlinePage(getCurrentProof(), getEnvironment());
               getEnvironment().getMediator().addKeYSelectionListener(keySelectionListener);
            }
         }
         return outline;
      }
      else if (Proof.class.equals(adapter)){
         return getCurrentProof();
      }
      else if (KeYEnvironment.class.equals(adapter)){
         return getEnvironment();
      }
      else if (UserInterface.class.equals(adapter)) {
         return getUI();
      }
      else if (IProofProvider.class.equals(adapter)) {
         return this;
      }
      else {
         return super.getAdapter(adapter);
      }
   }

   /**
    * This method is called when the proof is closed.
    * @param e The {@link ProofTreeEvent}.
    */
   protected void handleProofClosed(ProofTreeEvent e) {
      AutoModeTester.updateProperties(); // Make sure that start/stop auto mode buttons are disabled when the proof is closed interactively.
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addProofProviderListener(IProofProviderListener l) {
      if (l != null) {
         proofProviderListener.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeProofProviderListener(IProofProviderListener l) {
      if (l != null) {
         proofProviderListener.remove(l);
      }
   }
   
   /**
    * Informs all registered {@link IProofProviderListener} about the event.
    * @param e The {@link ProofProviderEvent}.
    */
   protected void fireCurrentProofsChanged(ProofProviderEvent e) {
      IProofProviderListener[] toInform = proofProviderListener.toArray(new IProofProviderListener[proofProviderListener.size()]);
      for (IProofProviderListener l : toInform) {
         l.currentProofsChanged(e);
      }
   }
}