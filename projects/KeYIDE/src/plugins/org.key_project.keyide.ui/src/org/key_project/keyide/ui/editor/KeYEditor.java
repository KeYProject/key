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
import java.io.File;
import java.util.LinkedList;
import java.util.List;

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
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.dialogs.SaveAsDialog;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.keyide.ui.editor.input.ProofOblInputEditorInput;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.util.LogUtil;
import org.key_project.keyide.ui.views.ProofTreeContentOutlinePage;
import org.key_project.util.eclipse.ResourceUtil;

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
   
   private boolean dirtyFlag = false;
      
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   private Proof proof;

   private Node showNode; 
   
   private ProofSourceViewerDecorator textViewer; // TODO: Rename, into proofDecorator. And also its getter

   private ProofTreeContentOutlinePage outline;
   
   /**
    * Contains the registered {@link IProofProviderListener}.
    */
   private List<IProofProviderListener> proofProviderListener = new LinkedList<IProofProviderListener>();
   
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
         handleProofClosed(e);
      }
   };
   
   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         // TODO: Refactor functionality into KeYEditor#handleMouseMoved(MouseEvent) which is called here
         if (showNode.getAppliedRuleApp() == null){
            textViewer.setBackgroundColorForHover();
         }
      }
   };

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
    * {@inheritDoc}
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      super.init(site, input);
   }
   
   @Override
   protected void doSetInput(IEditorInput input) throws CoreException {
      try {
         super.doSetInput(input);
         if (this.environment == null || this.proof == null) {
            if (input instanceof ProofOblInputEditorInput) {
               ProofOblInputEditorInput in = (ProofOblInputEditorInput) input;
               if (in.isInUse()) {
                  throw new CoreException(LogUtil.getLogger().createErrorStatus("Multiple editors of the same proof are currently not supported."));
               }
               else {
                  in.setInUse(true);
               }
               this.environment = in.getEnvironment();
               this.proof = environment.createProof(in.getProblem());
               this.environment.getMediator().setProof(proof);
               this.environment.getMediator().setStupidMode(true);
            }
            else if (input instanceof FileEditorInput) {
               FileEditorInput fileInput = (FileEditorInput) input;
               File file = ResourceUtil.getLocation(fileInput.getFile());
               Assert.isTrue(file != null, "File \"" + fileInput.getFile() + "\" is not local.");
               this.environment = KeYEnvironment.load(file, null, null);
               this.environment.getMediator().setStupidMode(true);
               Assert.isTrue(getEnvironment().getLoadedProof() != null, "No proof loaded.");
               this.proof = getEnvironment().getLoadedProof();
            }
         }
         else {
            setShowNode(showNode);
         }
      }
      catch (CoreException e) {
         throw e;
      }
      catch (Exception e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      super.createPartControl(parent);
      getEnvironment().getMediator().addKeYSelectionListener(keySelectionListener);
      getUI().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      ISourceViewer sourceViewer = getSourceViewer();
      textViewer = new ProofSourceViewerDecorator(sourceViewer);
      getCurrentProof().addProofTreeListener(proofTreeListener);
      sourceViewer.setEditable(false);
      sourceViewer.getTextWidget().addMouseMoveListener(mouseMoveListener);
      if (this.getShowNode() != null) {
         setShowNode(proof.root());
      }
      else {
         Node mediatorNode = environment.getMediator().getSelectedNode();
         setShowNode(mediatorNode != null ? mediatorNode : getCurrentProof().root());
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
      if (getUI() != null) {
         getUI().removePropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      }
      if (environment != null) {
         environment.getMediator().removeKeYSelectionListener(keySelectionListener);
      }
      if (proof != null) {
         proof.removeProofTreeListener(proofTreeListener);
      }
      if (outline != null) {
         outline.dispose();         
      }
      if (proof != null) {
         proof.dispose();
      }
      if (environment != null) {
         environment.dispose();
      }
      super.dispose();
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
      if(input instanceof ProofOblInputEditorInput){
         IMethod method = ((ProofOblInputEditorInput)input).getMethod();
         IPath methodPath = method.getPath();
         methodPath = methodPath.removeLastSegments(1);
         String name = getCurrentProof().name().toString();
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
   }
   
   private void save(IPath path) {
      try {
         if (path != null) {
            IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
            KeYUtil.saveProof(showNode.proof(), file);
            setDirtyFlag(false);
            FileEditorInput fileInput = new FileEditorInput(file);
            doSetInput(fileInput);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
   }

   private void setDirtyFlag(boolean dirtyFlag){
      this.dirtyFlag = dirtyFlag;
      getSite().getShell().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            firePropertyChange(PROP_DIRTY);
         }
      });
   }

   /**
    * This method is called when the proof is closed.
    * @param e The {@link ProofTreeEvent}.
    */
   protected void handleProofClosed(ProofTreeEvent e) {
      AutoModeTester.updateProperties(); // Make sure that start/stop auto mode buttons are disabled when the proof is closed interactively.
   }

   protected void handleProofChanged(ProofTreeEvent e) {
      setDirtyFlag(true);
   }
   
   @Override
   public boolean isDirty(){
      return dirtyFlag;
   }
   
   public Node getShowNode() { // TODO: Document method getShowNode()
      return showNode;
   }
   
   /**
    * Sets the showNode and the {@link Document} for the {@link ISourceViewer} of the {@link ProofSourceViewerDecorator}.
    * @param showNode the new shown {@link Node}.
    */
   public void setShowNode(Node showNode) {
      this.showNode=showNode;
      getEnvironment().getMediator().setStupidMode(true);
      textViewer.setDocumentForNode(showNode, getEnvironment().getMediator());
      if(showNode.getAppliedRuleApp() != null){
         PosInOccurrence posInOcc = showNode.getAppliedRuleApp().posInOccurrence();
         textViewer.setGreenBackground(posInOcc);
      }
   }
   
   public ProofSourceViewerDecorator getTextViewer() {
      return textViewer;
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
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
      return environment;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getCurrentProof() {
      return proof;
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
   public CustomConsoleUserInterface getUI() {
      KeYEnvironment<CustomConsoleUserInterface> environment = getEnvironment();
      return environment != null ? environment.getUi() : null;
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
