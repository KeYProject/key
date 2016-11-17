package org.key_project.sed.key.ui.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.action.GroupMarker;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.editors.text.TextEditorActionContributor;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.keyide.ui.composite.ProofTreeComposite;
import org.key_project.keyide.ui.editor.IPosInSequentProvider;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.editor.SequentEditor;
import org.key_project.keyide.ui.editor.input.TextEditorInput;
import org.key_project.keyide.ui.util.IProofNodeSearchSupport;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.ShowSubtreeOfNodeHandler;
import org.key_project.sed.key.ui.propertyTester.AutoModePropertyTesterSED;
import org.key_project.sed.ui.visualization.view.AbstractLaunchViewBasedEditorInViewView;
import org.key_project.util.eclipse.view.editorInView.EditorInViewEditorSite.RegisteredContextMenu;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The view based on the {@link IDebugView} which shows the {@link Proof}.
 * @author Seena Vellaramkalayil
 */
public class ProofView extends AbstractLaunchViewBasedEditorInViewView<SequentEditor, TextEditorActionContributor> implements IProofProvider, ITabbedPropertySheetPageContributor, IProofNodeSearchSupport, IPosInSequentProvider {
   /**
    * The unique id of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.key.ui.ProofView";
   
   /**
    * The message which is shown in case the currently selected {@link IDebugTarget} does not provide a {@link Proof}.
    */
   public static final String MESSAGE_DEBUG_TARGET_PROVIDES_NO_PROOF = "The currently selected debug target does not provide a proof.";

   /**
    * The {@link ProofTreeComposite} which shows the proof tree.
    */
   private ProofTreeComposite proofTreeComposite;
   
   /**
    * Listens for selection changes on {@link #treeViewer}.
    */
   private final ISelectionChangedListener treeViewerSelectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleTreeViewerSelectionChanged(event);
      }
   };
   
   /**
    * the {@link State} for showing the subtree of a node.
    */
   private State subtreeState;
   
   /**
    * the {@link IStateListener} to listen to changes on the subtreeState.
    */
   private final IStateListener subtreeStateListener = new IStateListener() {
      /**
       * {@inheritDoc}
       */
      @Override
      public void handleStateChange(State state, Object oldValue) {
         handleSubtreeStateChanged(state);
      }
   };
   
   /**
    * Contains the registered {@link IProofProviderListener}.
    */
   private final List<IProofProviderListener> proofProviderListener = new LinkedList<IProofProviderListener>();
   
   /**
    * The {@link KeYDebugTarget} which offers the currently shown {@link Proof}.
    */
   private KeYDebugTarget keyDebugTarget;
   
   /**
    * the {@link KeYEnvironment} of the proof.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * The shown {@link Proof}.
    */
   private Proof proof;
   
   /**
    * the currently loaded {@link IProject}.
    */
   private IProject currentProject;
   
   /**
    * The selected {@link IKeYSENode} in {@link #baseView}.
    */
   private IKeYSENode<?> baseViewNode;
   
   /**
    * the {link RuleAppListener} listening to rule applications.
    */
   private final RuleAppListener ruleAppListener = new RuleAppListener() {
      /**
       * {@inheritDoc}
       */
      @Override
      public void ruleApplied(final ProofEvent e) {
         getSite().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               handleRuleApplied(e);
            }
         });
      }
   };
   
   /**
    * the {@link AutoModeListener}.
    */
   private final AutoModeListener autoModeListener = new AutoModeListener() {
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
    * Listens for dispose changes on {@link #proof}.
    */
   private final ProofDisposedListener proofDisposedListener = new ProofDisposedListener() {
      @Override
      public void proofDisposing(ProofDisposedEvent e) {
      }
      
      @Override
      public void proofDisposed(ProofDisposedEvent e) {
         handleProofDisposed(e);
      }
   };

   /**
    * Constructor.
    */
   public ProofView() {
      ICommandService service = (ICommandService) PlatformUI.getWorkbench().getService(ICommandService.class);
      if (service != null) {
         Command subtreeCmd = service.getCommand(ShowSubtreeOfNodeHandler.COMMAND_ID);
         if (subtreeCmd != null) {
            subtreeState = subtreeCmd.getState(RegistryToggleState.STATE_ID);
            if (subtreeState != null) {
               subtreeState.addListener(subtreeStateListener);
            }
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (proofTreeComposite != null) {
         proofTreeComposite.dispose();
      }
      if (subtreeState != null) {
         subtreeState.removeListener(subtreeStateListener);
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Composite createEditorComposite(Composite parent) {
      SashForm parentComposite = new SashForm(parent, SWT.HORIZONTAL);
      // Proof tree composite
      proofTreeComposite = new ProofTreeComposite(parentComposite, SWT.NONE, SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL | SWT.BORDER, proof, environment);
      proofTreeComposite.getTreeViewer().addSelectionChangedListener(treeViewerSelectionListener);
      //create editor
      super.createEditorComposite(parentComposite);
      parentComposite.setWeights(new int[]{15, 85}); 
      parentComposite.setOrientation(SWT.HORIZONTAL);
      getSite().setSelectionProvider(proofTreeComposite.getTreeViewer());
      //update viewers if debugView is already open
      updateProofTreeViewer();
      if ((boolean) subtreeState.getValue()) {
         showSubtree(true);
      }
      createTreeViewerContextMenu();
      createTextEditorContextMenu();
      return parentComposite;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void editorPartControlCreated(SequentEditor editorPart, TextEditorActionContributor contributor) {
      super.editorPartControlCreated(editorPart, contributor);
      editorPart.addPropertyChangeListener(IPosInSequentProvider.PROP_SELECTED_POS_IN_SEQUENT, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            // Rethrow the event with changed source to own listener.
            firePropertyChange(evt.getPropertyName(), evt.getOldValue(), evt.getNewValue());
         }
      });
   }

   /**
    * method to create the context menu shown on this view's tree viewer.
    */
   protected void createTreeViewerContextMenu() {
      MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
      Menu menu = menuManager.createContextMenu(proofTreeComposite.getTreeViewer().getControl());
      proofTreeComposite.getTreeViewer().getControl().setMenu(menu);
      getSite().registerContextMenu("org.key_project.keyide.ui.view.outline.popup", menuManager, proofTreeComposite.getTreeViewer());
   }
   
   /**
    * method to create the context menu containing the available rules to apply on the proof.
    */
   protected void createTextEditorContextMenu() {
      List<RegisteredContextMenu> menus = getVirtualEditorSite().getRegisteredContextMenus();
      for (RegisteredContextMenu menu : menus) {
         if (AbstractTextEditor.COMMON_EDITOR_CONTEXT_MENU_ID.equals(menu.getMenuId())) {
            getSite().registerContextMenu(getSourceViewerMenuId(), menu.getMenuManager(), menu.getSelectionProvider());
         }
      }
   }
   
   /**
    * returns the id of the context menu of the source viewer.
    * @return String id of the context menu
    */
   protected String getSourceViewerMenuId() {
      return VIEW_ID + ".popup";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected SequentEditor createEditorPart() {
      return new SequentEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected TextEditorActionContributor createEditorActionBarContributor() {
      return new TextEditorActionContributor() {
         @Override
         public void contributeToMenu(IMenuManager menu) {
            IMenuManager editMenu = menu.findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);
            GroupMarker findExtGroup = new GroupMarker(IWorkbenchActionConstants.FIND_EXT);
            editMenu.add(findExtGroup);
            super.contributeToMenu(menu);
         }

         @Override
         public void setActiveEditor(IEditorPart part) {
            super.setActiveEditor(part);
         }
      };
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput createEditorInput() {
      return new TextEditorInput(StringUtil.EMPTY_STRING, StringUtil.EMPTY_STRING);
   }
   
   /**
    * Updates the providers of {@link ProofView#getTreeViewer()} and {@link ProofView#getSourceViewer()}
    * and creates context menus. Selection is set to root.
    */
   protected void updateProofTreeViewer() {
      Assert.isNotNull(proofTreeComposite);
      if (proof != null) {
         //set default selection to root
         if (baseViewNode != null && (boolean) subtreeState.getValue()) {
            proofTreeComposite.selectNodeThreadSafe(baseViewNode.getExecutionNode().getProofNode());
         }
         else {
            proofTreeComposite.selectNodeThreadSafe(proof.root());
         }
      }
   }
   
   /**
    * handles the change in the subtreeState.
    * @param state The state that has changed; never null. The value for this state has been updated to the new value.
    */
   protected void handleSubtreeStateChanged(State state) {
      showSubtree(true);
   }
   
   /**
    * Shows a new sub tree.
    * @param keepSelection {@code true} keep selection, {@code false} do not keep selection
    */
   protected void showSubtree(boolean keepSelection) {
      if (proofTreeComposite != null) {
         if (baseViewNode != null && (boolean) subtreeState.getValue()) {
            proofTreeComposite.showSubtree(keepSelection, true, baseViewNode.getExecutionNode().getProofNode());
         }
         else {
            proofTreeComposite.showSubtree(keepSelection, false, null);
         }
      }
   }
   
   /**
    * When the selection on {@link #treeViewer} has changed.
    * @param event The selection changed event.
    */
   protected void handleTreeViewerSelectionChanged(SelectionChangedEvent event) {
      Node node = ProofTreeComposite.getSelectedNode(event.getSelection());
      showNode(node);
   }

   /**
    * Shows the given {@link Node}.
    * @param node The {@link Node} to show.
    */
   protected void showNode(Node node) {
      TermLabelVisibilityManager manager = getUI() != null ? getUI().getTermLabelVisibilityManager() : null;
      if (node != null) {
         getEditorPart().showNode(node, SymbolicExecutionUtil.createNotationInfo(getCurrentProof()), manager, manager);
      }
      else {
         getEditorPart().showNode(null, SymbolicExecutionUtil.createNotationInfo((Node) null), manager, manager);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void doUpdateEditorContent(Set<ISEDebugTarget> oldTargets, 
                                        Set<ISEDebugTarget> newTargets, 
                                        Object[] newElements) {
      if (!CollectionUtil.isEmpty(newTargets)) {
         // Find selected elements of interest (first selected IKeYSENode or a KeYDebugTarget otherwise)
         KeYDebugTarget keyTarget = null;
         IKeYSENode<?> seNode = null;
         if (newElements != null) {
            int i = 0;
            while (i < newElements.length && seNode == null) {
               Object element = newElements[i];
               if (element instanceof ILaunch) {
                  element = ((ILaunch) element).getDebugTarget();
               }
               if (element instanceof IKeYSENode<?>) {
                  IKeYSENode<?> node = (IKeYSENode<?>) element;
                  KeYDebugTarget target = node.getDebugTarget();
                  if (!target.isTerminated()) {
                     seNode = node;
                     keyTarget = target;
                  }
               }
               else if (element instanceof IDebugElement) {
                  IDebugTarget target = ((IDebugElement) element).getDebugTarget();
                  if (target instanceof KeYDebugTarget && !target.isTerminated()) {
                     keyTarget = (KeYDebugTarget) target;
                  }
               }
               i++;
            }
         }
         // Get new proof and its environment
         Proof newProof = null;
         SymbolicExecutionEnvironment<?> newEnvironment = null;
         IMethod newMethod = null;
         if (keyTarget != null) {
            newProof = keyTarget.getProof();
            newEnvironment = keyTarget.getEnvironment();
            newMethod = keyTarget.getMethod();
         }
         // Replace content.
         changeProof(keyTarget, newProof, newEnvironment, newMethod, seNode);
      }
      else {
         setMessage(MESSAGE_NO_DEBUG_TARGET_SELECTED);
      }
   }
   
   /**
    * Updates the shown proof.
    * @param newTarget The new {@link KeYDebugTarget}.
    * @param newProof The new {@link Proof}.
    * @param newEnvironment The new {@link SymbolicExecutionEnvironment}.
    * @param newMethod The new {@link IMethod}.
    * @param seNode The {@link IKeYSENode}.
    */
   protected void changeProof(KeYDebugTarget newTarget,
                              Proof newProof, 
                              SymbolicExecutionEnvironment<?> newEnvironment, 
                              IMethod newMethod, 
                              IKeYSENode<?> seNode) {
      keyDebugTarget = newTarget;
      // Replace content if needed
      if (newProof != proof) {
         // Remove listener from old proof
         if (environment != null) {
            environment.getProofControl().removeAutoModeListener(autoModeListener);
         }
         if (proof != null && !proof.isDisposed()) {
            proof.removeProofDisposedListener(proofDisposedListener);
            proof.removeRuleAppListener(ruleAppListener);
         }
         // Add listener to new proof
         proof = newProof;
         environment = newEnvironment;
         if (proofTreeComposite != null) { // Might be null when view is opened and a proof is already defined.
            proofTreeComposite.changeProof(newProof, newEnvironment);
         }
         if (environment != null) {
            environment.getProofControl().addAutoModeListener(autoModeListener);
            environment.getProofControl().setMinimizeInteraction(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter());
         }
         if (proof != null && !proof.isDisposed()) {
            if (proofTreeComposite != null) { // Might be null when view is opened and a proof is already defined.
               proofTreeComposite.showSubtree(false, false, proof.root());
            }
            proof.addProofDisposedListener(proofDisposedListener);
            proof.addRuleAppListener(ruleAppListener);
         }
         if (newMethod != null) {
            this.currentProject = newMethod.getResource().getProject();
         }
         else {
            this.currentProject = null;
         }
         if (proofTreeComposite != null) {
            updateProofTreeViewer();
         }
         fireCurrentProofsChanged(new ProofProviderEvent(this, getCurrentProofs(), getCurrentProof(), getUI(), getEnvironment()));
      }
      // Update message
      if (newProof != null && !newProof.isDisposed()) {
         setMessage(null);
      }
      else {
         setMessage(MESSAGE_DEBUG_TARGET_PROVIDES_NO_PROOF);
      }
      // Update selection
      if (seNode != baseViewNode) {
         baseViewNode = seNode;
         if ((boolean) subtreeState.getValue()) {
            showSubtree(false);
         }
         if (seNode != null) {
            if (proofTreeComposite != null) {
               Node keyNode = seNode.getExecutionNode().getProofNode();
               proofTreeComposite.selectNodeThreadSafe(keyNode);
            }
         }
      }
   }

   /**
    * handles the {@link ProofEvent} when a rule is applied manually. Updates selection.
    * @param e the {@link ProofEvent} to handle
    */
   protected void handleRuleApplied(ProofEvent e) {
      Node selectedNode = proofTreeComposite.getSelectedNode();
      if (selectedNode != null) {
         Node newNode = selectedNode;
         while (!newNode.leaf()) {
            newNode = newNode.child(0);
         }
         if (selectedNode != newNode) {
            proofTreeComposite.selectNodeThreadSafe(newNode);
         }
      }
   }

   /**
    * handles the {@link ProofEvent} when auto mode has stopped.
    * @param e the {@link ProofEvent} to handle
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (proof != null && !proof.isDisposed()) {
         proof.addRuleAppListener(ruleAppListener);
      }
      AutoModePropertyTesterSED.updateProperties();
   }

   /**
    * handles the {@link ProofEvent} when auto mode has started.
    * @param e the {@link ProofEvent} to handle
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (proof != null && !proof.isDisposed()) {
         proof.removeRuleAppListener(ruleAppListener);
      }
      AutoModePropertyTesterSED.updateProperties();
   }
   
   /**
    * When the current proof was disposed.
    * @param e The {@link ProofDisposedEvent}.
    */
   protected void handleProofDisposed(ProofDisposedEvent e) {
      if (proofTreeComposite != null && !proofTreeComposite.isDisposed()) {
         proofTreeComposite.getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               changeProof(keyDebugTarget, null, null, null, baseViewNode);
            }
         });
      }
   }

   /**
    * returns the currently loaded {@link IProject}.
    * @return the {@link IProject}
    */
   public IProject getProject() {
      return currentProject;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<?> getEnvironment() {
      return environment;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getCurrentProof() {
      return proof;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof[] getCurrentProofs() {
      return new Proof[] {proof};
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public UserInterfaceControl getUI() {
      return environment != null ? environment.getUi() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ProofControl getProofControl() {
      return environment != null ? environment.getProofControl() : null;
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

   /**
    * {@inheritDoc}
    */
   @Override
   public String getContributorId() {
      return KeYEditor.CONTRIBUTOR_ID;
   }

   /**
    * Returns the {@link KeYDebugTarget} from which the {@link Proof} is currently shown.
    * @return The {@link KeYDebugTarget} or {@code null} if not available.
    */
   public KeYDebugTarget getKeyDebugTarget() {
      return keyDebugTarget;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void openSearchPanel() {
      proofTreeComposite.openSearchPanel();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void closeSearchPanel() {
      proofTreeComposite.closeSearchPanel();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void searchText(String text) {
      proofTreeComposite.searchText(text);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void jumpToPreviousResult() {
      proofTreeComposite.jumpToPreviousResult();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void jumpToNextResult() {
      proofTreeComposite.jumpToNextResult();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInSequent getSelectedPosInSequent() {
      return getEditorPart().getSelectedPosInSequent();
   }

   /**
    * Returns the currently selected {@link Node}.
    * @return The currently selected {@link Node}.
    */
   public Node getSelectedNode() {
      return proofTreeComposite.getSelectedNode();
   }

   /**
    * Selects a given {@link Node}. 
    * @param node the {@link Node} to select
    */
   public void selectNode(Node node) {
      proofTreeComposite.selectNode(node);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanStartAutomode() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanApplyRules() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanPruneProof() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCanStartSMTSolver() {
      return true;
   }
}
