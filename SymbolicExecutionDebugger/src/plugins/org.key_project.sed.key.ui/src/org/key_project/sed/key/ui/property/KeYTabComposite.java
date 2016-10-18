/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package org.key_project.sed.key.ui.property;

import java.util.EventObject;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.keyide.ui.editor.SequentDisplaySettingsMenuFactory;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerEvent;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * This composite provides the content shown in {@link KeYDebugNodePropertySection}
 * and {@link KeYGraphitiDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public class KeYTabComposite extends Composite implements IProofProvider {
   /**
    * Shows the node id with applied rule of the node in KeY's proof tree represented by the current {@link IKeYSENode}.
    */
   private Text nodeText;
   
   /**
    * Shows the {@link Sequent} of the node in KeY's proof tree represented by the current {@link IKeYSENode}.
    */
   private SourceViewer sequentViewer;
   
   /**
    * The {@link ProofSourceViewerDecorator} used to decorate {@link #sequentViewer}.
    */
   private ProofSourceViewerDecorator sequentViewerDecorator;
   
   /**
    * The {@link Font} of {@link #sequentViewer} which needs to be disposed manually.
    */
   private Font viewerFont;
   
   /**
    * The currently shown {@link IKeYSENode}.
    */
   private IKeYSENode<?> node;
   
   /**
    * The currently shown {@link Node}.
    */
   private Node keyNode;
   
   /**
    * Contains the registered {@link IProofProviderListener}.
    */
   private final List<IProofProviderListener> proofProviderListener = new LinkedList<IProofProviderListener>();
   
   /**
    * Listens for editor changes.
    */
   private IPropertyChangeListener editorsListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handleEditorPropertyChange(event);
      }
   };

   /**
    * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
    */
   private final SettingsListener viewSettingsListener = new SettingsListener() {
      @Override
      public void settingsChanged(EventObject e) {
         handleViewSettingsChanged(e);
      }
   };
   
   /**
    * Observes changes on the used {@link TermLabelVisibilityManager}.
    */
   private final TermLabelVisibilityManagerListener termLabelVisibilityManagerListener = new TermLabelVisibilityManagerListener() {
      @Override
      public void visibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
         handleVisibleLabelsChanged(e);
      }
   };
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public KeYTabComposite(Composite parent, int style, TabbedPropertySheetWidgetFactory factory) {
      super(parent, style);
      setLayout(new FillLayout());
      
      Composite composite = factory.createFlatFormComposite(this);

      nodeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      nodeText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nodeText.setLayoutData(data);

      CLabel nodeLabel = factory.createCLabel(composite, "Node:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nodeText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nodeText, 0, SWT.CENTER);
      nodeLabel.setLayoutData(data);

      sequentViewer = new SourceViewer(composite, null, SWT.MULTI | SWT.BORDER | SWT.FULL_SELECTION);
      sequentViewer.setEditable(false);
      updateSequentViewerFont();
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nodeText, 0, ITabbedPropertyConstants.VSPACE);
      sequentViewer.getControl().setLayoutData(data);
      sequentViewerDecorator = new ProofSourceViewerDecorator(sequentViewer);
      MenuManager sequentManager = new MenuManager();
      sequentManager.add(SequentDisplaySettingsMenuFactory.createSequentDisplaySettingsMenu(this));
      sequentViewer.getControl().setMenu(sequentManager.createContextMenu(sequentViewer.getControl()));
      
      CLabel sequentLabel = factory.createCLabel(composite, "Sequent:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(sequentViewer.getControl(), -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(sequentViewer.getControl(), 0, SWT.TOP);
      sequentLabel.setLayoutData(data);

      SWTUtil.getEditorsPreferenceStore().addPropertyChangeListener(editorsListener);
      JFaceResources.getFontRegistry().addListener(editorsListener);
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().addSettingsListener(viewSettingsListener);
   }

   /**
    * When a property of the text editor has changed.
    * @param event The {@link PropertyChangeEvent}.
    */
   protected void handleEditorPropertyChange(PropertyChangeEvent event) {
      if (event.getProperty().equals(SWTUtil.getEditorsTextFontPropertiesKey())) {
         updateSequentViewerFont();
      }
   }

   /**
    * Updates the font of {@link #sequentViewer}.
    */
   protected void updateSequentViewerFont() {
      if (viewerFont != null) {
         viewerFont.dispose();
      }
      viewerFont = SWTUtil.initializeViewerFont(sequentViewer);
   }

   /**
    * Updates the shown content.
    * @param node The {@link IKeYSENode} which provides the new content.
    */
   public void updateContent(IKeYSENode<?> node) {
      Proof oldProof = getCurrentProof();
      if (this.node != null) {
         getTermLabelVisibilityManager().removeTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);
      }
      this.node = node;
      if (this.node != null) {
         getTermLabelVisibilityManager().addTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);
      }
      String name = null;
      if (node != null) {
         keyNode = node.getExecutionNode().getProofNode();
         name = keyNode.serialNr() + ": " + keyNode.name(); // Copied from ProofRenderer
      }
      else {
         keyNode = null;
      }
      SWTUtil.setText(nodeText, name);
      updateShownSequent();
      if (!ObjectUtil.equals(oldProof, getCurrentProof())) {
         fireCurrentProofsChanged(new ProofProviderEvent(this, getCurrentProofs(), getCurrentProof(), getUI(), getEnvironment()));
      }
   }
   
   /**
    * Updates the shown sequent.
    */
   protected void updateShownSequent() {
      if (keyNode != null && !keyNode.proof().isDisposed()) {
         sequentViewerDecorator.showNode(keyNode, SymbolicExecutionUtil.createNotationInfo(keyNode), getTermLabelVisibilityManager());
      }
      else {
         sequentViewerDecorator.showNode(null, SymbolicExecutionUtil.createNotationInfo(keyNode), getTermLabelVisibilityManager());
      }
   }

   /**
    * When the settings of {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()} have changed.
    * @param e The event.
    */
   protected void handleViewSettingsChanged(EventObject e) {
      updateShownSequentThreadSave();
   }

   /**
    * When the visible term labels have changed.
    * @param e The event.
    */
   protected void handleVisibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
      updateShownSequentThreadSave();
   }
   
   /**
    * Updates the shown {@link Sequent} thread save.
    */
   protected void updateShownSequentThreadSave() {
      getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            updateShownSequent();
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().removeSettingsListener(viewSettingsListener);
      if (node != null) {
         getTermLabelVisibilityManager().removeTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);
      }
      JFaceResources.getFontRegistry().removeListener(editorsListener);
      SWTUtil.getEditorsPreferenceStore().removePropertyChangeListener(editorsListener);
      if (viewerFont != null) {
         viewerFont.dispose();
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getCurrentProof() {
      return keyNode != null ? keyNode.proof() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof[] getCurrentProofs() {
      Proof proof = getCurrentProof();
      return proof != null ? new Proof[] {proof} : new Proof[0];
   }
   
   /**
    * Returns the {@link KeYDebugTarget} if available and {@code null} otherwise.
    * @return The {@link KeYDebugTarget} of the currently shown {@link IKeYSENode} or {@code null} otherwise.
    */
   public KeYDebugTarget getDebugTarget() {
      return node != null ? node.getDebugTarget() : null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public SymbolicExecutionEnvironment<?> getEnvironment() {
      KeYDebugTarget target = getDebugTarget();
      return target != null ? target.getEnvironment() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public UserInterfaceControl getUI() {
      SymbolicExecutionEnvironment<?> env = getEnvironment();
      return env != null ? env.getUi() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ProofControl getProofControl() {
      UserInterfaceControl ui = getUI();
      return ui != null ? ui.getProofControl() : null;
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
    * {@inheritDoc}
    */
   @Override
   public IProject getProject() {
      KeYDebugTarget target = getDebugTarget();
      IMethod method = target != null ? target.getMethod() : null;
      return method != null ? method.getResource().getProject() : null;
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

   /**
    * Returns the used {@link TermLabelVisibilityManager}.
    * @return The used {@link TermLabelVisibilityManager} or {@code null} if not available.
    */
   public TermLabelVisibilityManager getTermLabelVisibilityManager() {
      UserInterfaceControl ui = getUI();
      return ui != null ? ui.getTermLabelVisibilityManager() : null; 
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanStartAutomode() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanApplyRules() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanPruneProof() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanStartSMTSolver() {
      return false;
   }
}