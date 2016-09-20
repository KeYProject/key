package org.key_project.sed.key.ui.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.EventObject;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.views.properties.IPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.keyide.ui.editor.IPosInSequentProvider;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.handlers.ShowSymbolicExecutionTreeOnlyHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.keyide.ui.views.ProofTreeContentOutlinePage;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.ShowSubtreeOfNodeHandler;
import org.key_project.sed.key.ui.propertyTester.AutoModePropertyTesterSED;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The view based on the {@link IDebugView} which shows the {@link Proof}.
 * @author Seena Vellaramkalayil
 */
public class ProofView extends AbstractViewBasedView implements IProofProvider, ITabbedPropertySheetPageContributor, IPosInSequentProvider {   
   /**
    * the unique id of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.key.ui.ProofView";
   
   /**
    * The used {@link PropertyChangeSupport}.
    */
   private final PropertyChangeSupport pcs = new PropertyChangeSupport(this);
   
   /**
    * Contains the registered {@link IProofProviderListener}.
    */
   private final List<IProofProviderListener> proofProviderListener = new LinkedList<IProofProviderListener>();

   /**
    * the {@link SashForm} to divide {@link TreeViewer} and {@link SourceViewer}.
    */
   private SashForm parentComposite;

   /**
    * the {@link TreeViewer} of this view.
    */
   private TreeViewer treeViewer;

   /**
    * the {@link SourceViewer} of this view.
    */
   private SourceViewer sourceViewer;
   
   /**
    * the {@link IDebugView} this view is based on.
    */
   private IViewPart baseView;
   
   /**
    * The selected {@link IKeYSENode} in {@link #baseView}.
    */
   private IKeYSENode<?> baseViewNode;

   /**
    * the loaded {@link Proof}.
    */
   private Proof proof;

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
    * the {@link LazyProofTreeContentProvider} of the treeViewer.
    */
   private LazyProofTreeContentProvider contentProvider;

   /**
    * the {@link ProofTreeLabelProvider} of the treeViewer.
    */
   private ProofTreeLabelProvider labelProvider;

   /**
    * The {@link KeYDebugTarget} which offers the currently shown {@link Proof}.
    */
   private KeYDebugTarget keyDebugTarget;
   
   /**
    * the {@link KeYEnvironment} of the proof.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * the {@link ProofSourceViewerDecorator} of the sourceViewer.
    */
   private ProofSourceViewerDecorator sourceViewerDecorator;
   
   /**
    * the currently loaded {@link IProject}.
    */
   private IProject currentProject;
   
   /**
	 * The {@link State} which indicates hiding or showing of intermediate proof steps.
	 */
	private State hideState;
	
	/**
	 * the {@link State} for the show symbolic execution tree only outline filter.
	 */
	private State symbolicState;
	
	/**
	 * the {@link State} for showing the subtree of a node.
	 */
	private State subtreeState;
	
   /**
    * the {@link ISelectionChangedListener} for the {@link IDebugView}.
    */
   private final ISelectionChangedListener baseViewListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleBaseViewSelectionChanged(event.getSelection());
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
    * the {@link IMenuListener} listening to actions on the context menu of the sourceViewer.
    */
   private final IMenuListener contextMenuListener = new IMenuListener() {
      /**
       * {@inheritDoc}
       */
      @Override
      public void menuAboutToShow(IMenuManager manager) {
         if (getSourceViewerMenuId().equals(manager.getId())) {
            manager.add(new Separator(IWorkbenchActionConstants.GROUP_ADD));
         }
      }
   };
   
   /**
	 * The {@link IStateListener} to sync the hide intermediate proof steps toggleState with the outline page.
	 */
	private final IStateListener hideStateListener = new IStateListener() {
		@Override
		public void handleStateChange(State state, Object oldValue) {
		   contentProvider.setHideState((boolean) state.getValue());
			handleHideSymbolicStateChanged(state, oldValue);
		}
	};
	
	/**
	 * the {@link IStateListener} to sync the show symbolic execution tree only toggleState with the outline page.
	 */
	private final IStateListener symbolicStateListener = new IStateListener() {
	   /**
	    * {@inheritDoc}
	    */
      @Override
      public void handleStateChange(State state, Object oldValue) {
         contentProvider.setSymbolicState((boolean) state.getValue());
         handleHideSymbolicStateChanged(state, oldValue);
      }
	};
	
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
	 * the {link RuleAppListener} listening to rule applications.
	 */
	private final RuleAppListener ruleAppListener = new RuleAppListener() {
		/**
		 * {@inheritDoc}
		 */
		@Override
		public void ruleApplied(final ProofEvent e) {
	      treeViewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               handleRuleApplied(e);
            }
	      });
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
	 * the constructor of the class.
	 */
	public ProofView() {
      ICommandService service = (ICommandService) PlatformUI.getWorkbench().getService(ICommandService.class);
      if (service != null) {
         Command hideCmd = service.getCommand(HideIntermediateProofstepsHandler.COMMAND_ID);
         if (hideCmd != null) {
            hideState = hideCmd.getState(RegistryToggleState.STATE_ID);
            if (hideState != null) {
               hideState.addListener(hideStateListener);
            }
         }
         Command symbolicCmd = service.getCommand(ShowSymbolicExecutionTreeOnlyHandler.COMMAND_ID);
         if (symbolicCmd != null) {
            symbolicState = symbolicCmd.getState(RegistryToggleState.STATE_ID);
            if (symbolicState != null) {
               symbolicState.addListener(symbolicStateListener);
            }
         }
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
	 * handles the {@link ProofEvent} when a rule is applied manually. Updates selection.
	 * @param e the {@link ProofEvent} to handle
	 */
	protected void handleRuleApplied(ProofEvent e) {
	   Node selectedNode = getSelectedNode();
	   if (selectedNode != null) {
	      Node newNode = selectedNode;
	      while (!newNode.leaf()) {
	         newNode = newNode.child(0);
	      }
	      if (selectedNode != newNode) {
	         selectNodeThreadSafe(newNode);
	      }
	   }
	}
	
	/**
	 * Handles a change in the state of the hideIntermediateProofsteps and showSymbolicExecutionNodes filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleHideSymbolicStateChanged(State state, Object oldValue) {
		Node currentSelection = getSelectedNode();
		treeViewer.setInput(proof);
		if (currentSelection != null) {
		   selectNodeThreadSafe(currentSelection);
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
      if (proof != null && treeViewer != null) {
         Node currentSelection = getSelectedNode();
         if (baseViewNode != null && (boolean) subtreeState.getValue()) {
            contentProvider.setShowSubtreeState(true, baseViewNode.getExecutionNode().getProofNode());
         }
         else {
            contentProvider.setShowSubtreeState(false, proof.root());
         }
         treeViewer.setInput(proof);
         if (currentSelection != null && keepSelection) {
            selectNodeThreadSafe(currentSelection);
         }
      }
   }
	
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      parentComposite = new SashForm(parent, SWT.HORIZONTAL);
      //create tree viewer
      this.treeViewer = new TreeViewer(parentComposite, SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL | SWT.BORDER);
      treeViewer.setUseHashlookup(true);
      this.contentProvider = new LazyProofTreeContentProvider(environment != null ? environment.getProofControl() : null);
      contentProvider.setHideState((boolean) hideState.getValue());
      contentProvider.setSymbolicState((boolean) symbolicState.getValue());
      treeViewer.setContentProvider(contentProvider);
      treeViewer.addSelectionChangedListener(treeViewerSelectionListener);
      //create source viewer
      this.sourceViewer = new SourceViewer(parentComposite, null, SWT.MULTI | SWT.BORDER | SWT.FULL_SELECTION | SWT.H_SCROLL | SWT.V_SCROLL);
      sourceViewer.setEditable(false);
      final Font font = SWTUtil.initializeViewerFont(sourceViewer);
      sourceViewer.getTextWidget().addDisposeListener(new DisposeListener() {
         @Override
         public void widgetDisposed(DisposeEvent e) {
            if (font != null) {
               font.dispose();
            }
         }
      });
      parentComposite.setWeights(new int[]{15, 85}); 
      parentComposite.setOrientation(SWT.HORIZONTAL);
      FormData data = new FormData();
      sourceViewer.getControl().setLayoutData(data);
      sourceViewerDecorator = new ProofSourceViewerDecorator(sourceViewer);
      sourceViewerDecorator.addPropertyChangeListener(ProofSourceViewerDecorator.PROP_SELECTED_POS_IN_SEQUENT, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            handleViewerDecoratorSelectedPosInSequentChanged(evt);
         }
      });
      getSite().setSelectionProvider(treeViewer);
      //update viewers if debugView is already open
      updateViewer();
      if ((boolean) subtreeState.getValue()) {
         showSubtree(true);
      }
      createTreeViewerContextMenu();
      createSourceViewerContextMenu();
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().addSettingsListener(viewSettingsListener);
   }
   
   /**
    * When the selected {@link PosInSequent} in {@link #sourceViewerDecorator} has changed.
    * @param evt The event.
    */
   protected void handleViewerDecoratorSelectedPosInSequentChanged(PropertyChangeEvent evt) {
      pcs.firePropertyChange(PROP_SELECTED_POS_IN_SEQUENT, evt.getOldValue(), evt.getNewValue());
   }

   /**
    * method to create the context menu shown on this view's tree viewer.
    */
   protected void createTreeViewerContextMenu() {
      MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
      Menu menu = menuManager.createContextMenu(treeViewer.getControl());
      treeViewer.getControl().setMenu(menu);
      getSite().registerContextMenu("org.key_project.keyide.ui.view.outline.popup", menuManager, treeViewer);
   }
   
   /**
    * method to create the context menu containing the available rules to apply on the proof.
    */
   protected void createSourceViewerContextMenu() {
      StyledText styledText = sourceViewer.getTextWidget();
      MenuManager menuMgr = new MenuManager(getSourceViewerMenuId(), getSourceViewerMenuId());
      menuMgr.setRemoveAllWhenShown(true);
      menuMgr.addMenuListener(contextMenuListener);
      Menu menu = menuMgr.createContextMenu(styledText);
      styledText.setMenu(menu);
      getSite().registerContextMenu(getSourceViewerMenuId(), menuMgr, sourceViewer);
   }

   /**
    * When the settings of {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()} have changed.
    * @param e The event.
    */
   protected void handleViewSettingsChanged(EventObject e) {
      getSite().getShell().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            showNode(getSelectedNode());
         }
      });
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IPropertySheetPage.class.equals(adapter)) {
         final TabbedPropertySheetPage pcp = new TabbedPropertySheetPage(this);
         // Make sure that initial content is shown even if the focus is set to the outline view and not to the editor. 
         getSite().getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if (!pcp.getControl().isDisposed()) {
                  pcp.selectionChanged(ProofView.this, treeViewer.getSelection());
               }
            }
         });
         return pcp;
      }
      else if (IProofProvider.class.equals(adapter)) {
         return this;
      }
      else {
         return super.getAdapter(adapter);
      }
   }

   /**
    * When the selection on {@link #treeViewer} has changed.
    * @param event The selection changed event.
    */
   protected void handleTreeViewerSelectionChanged(SelectionChangedEvent event) {
      Node node = getNode(event.getSelection());
      showNode(node);
   }
   
   /**
    * Shows the given {@link Node}.
    * @param node The {@link Node} to show.
    */
   protected void showNode(Node node) {
      if (node != null) {
         sourceViewerDecorator.showNode(node, SymbolicExecutionUtil.createNotationInfo(getCurrentProof()));
      }
      else {
         sourceViewerDecorator.showNode(null, SymbolicExecutionUtil.createNotationInfo((Node) null));
      }
   }
   
   /**
    * When the current proof was disposed.
    * @param e The {@link ProofDisposedEvent}.
    */
   protected void handleProofDisposed(ProofDisposedEvent e) {
      if (treeViewer != null && !treeViewer.getControl().isDisposed()) {
         treeViewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               changeProof(keyDebugTarget, null, null, null, baseViewNode);
            }
         });
      }
   }
   
   /**
    * changes the currently shown proof if there is a selection change on the {@link DebugView}.
    * @param selection the current selection on {@link DebugView}
    */
   protected void handleBaseViewSelectionChanged(ISelection selection) {
      // Find selected elements of interest (first selected IKeYSENode or a KeYDebugTarget otherwise)
      Object[] elements = SWTUtil.toArray(selection);
      KeYDebugTarget keyTarget = null;
      IKeYSENode<?> seNode = null;
      if (elements != null) {
         int i = 0;
         while (i < elements.length && seNode == null) {
            Object element = elements[i];
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
         if (contentProvider != null) { // Might be null when view is opened and a proof is already defined.
            contentProvider.setProofControl(environment != null ? environment.getProofControl() : null);
         }
         if (environment != null) {
            environment.getProofControl().addAutoModeListener(autoModeListener);
            environment.getProofControl().setMinimizeInteraction(true);
         }
         if (proof != null && !proof.isDisposed()) {
            if (contentProvider != null) { // Might be null when view is opened and a proof is already defined.
               contentProvider.setShowSubtreeState(false, proof.root());
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
         if (treeViewer != null && sourceViewer != null) {
            updateViewer();
         }
         fireCurrentProofsChanged(new ProofProviderEvent(this, getCurrentProofs(), getCurrentProof(), getUI(), getEnvironment()));
      }
      // Update selection
      if (seNode != baseViewNode) {
         baseViewNode = seNode;
         if ((boolean) subtreeState.getValue()) {
            showSubtree(false);
         }
         if (seNode != null) {
            if (treeViewer != null && sourceViewer!= null) {
               Node keyNode = seNode.getExecutionNode().getProofNode();
               selectNodeThreadSafe(keyNode);
            }
         }
      }
   }

   /**
    * Updates the providers of {@link ProofView#getTreeViewer()} and {@link ProofView#getSourceViewer()}
    * and creates context menus. Selection is set to root.
    */
   protected void updateViewer() {
      Assert.isNotNull(treeViewer);
      Assert.isNotNull(sourceViewer);
      Assert.isNotNull(sourceViewerDecorator);
      if (proof != null) {
         treeViewer.setInput(proof);
         if (labelProvider != null) {
            labelProvider.dispose();
         }
         labelProvider = new ProofTreeLabelProvider(treeViewer, environment.getProofControl(), proof);
         treeViewer.setLabelProvider(labelProvider);
         contentProvider.injectTopLevelElements();
         //set default selection to root
         if (baseViewNode != null && (boolean) subtreeState.getValue()) {
            selectNodeThreadSafe(baseViewNode.getExecutionNode().getProofNode());
         }
         else {
            selectNodeThreadSafe(proof.root());
         }
      }
      else {
         treeViewer.setInput(null);
      }
      sourceViewer.getTextWidget().layout();
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
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      if (treeViewer != null && !treeViewer.getControl().isDisposed()) {
         treeViewer.getControl().setFocus();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().removeSettingsListener(viewSettingsListener);
      if (parentComposite != null) {
         parentComposite.dispose();
      }
      if (treeViewer != null) {
         treeViewer.removeSelectionChangedListener(treeViewerSelectionListener);
         treeViewer.getControl().dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      if (sourceViewer != null) {
         sourceViewer.getControl().dispose();
      }
      if (environment != null) {
         environment.getProofControl().removeAutoModeListener(autoModeListener);
      }
      if (baseView != null) {
         baseView.getSite().getSelectionProvider().removeSelectionChangedListener(baseViewListener);
      }
      if (proof != null && !proof.isDisposed()) {
         proof.removeProofDisposedListener(proofDisposedListener);
         proof.removeRuleAppListener(ruleAppListener);
      }
      if (hideState != null) {
    	  hideState.removeListener(hideStateListener);
      }
      if (symbolicState != null) {
    	  symbolicState.removeListener(symbolicStateListener);
      }
      if (subtreeState != null) {
         subtreeState.removeListener(subtreeStateListener);
      }     
      super.dispose();
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
   public PosInSequent getSelectedPosInSequent() {
      return sourceViewerDecorator.getSelectedPosInSequent();
   }
   
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
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseViewReference(IViewReference baseViewReference) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(baseViewReference.getId());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseView(IViewPart view) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(view.getSite().getId());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView) {
      if (oldBaseView != null) {
         oldBaseView.getSite().getSelectionProvider().removeSelectionChangedListener(baseViewListener);
      }
      if (newBaseView != null) {
         this.baseView = newBaseView;
         ISelectionProvider selectionProvider = baseView.getSite().getSelectionProvider();
         selectionProvider.addSelectionChangedListener(baseViewListener);
         handleBaseViewSelectionChanged(selectionProvider.getSelection());
      }
   }
   
   /**
    * method to select a node thread safe.
    * @param node the {@link Node} to select
    */
   protected void selectNodeThreadSafe(final Node node) {
      if (!treeViewer.getControl().getDisplay().isDisposed()) {
         treeViewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!treeViewer.getControl().isDisposed()) {
                  selectNode(node);
               }
            }
         });
      }
   }
   
	/**
	 * Selects a given {@link Node}. 
	 * @param node the {@link Node} to select
	 */
   public void selectNode(Node node) {
      ProofTreeContentOutlinePage.makeSureElementIsLoaded(node, treeViewer, contentProvider);
      treeViewer.setSelection(SWTUtil.createSelection(node), true);
   }
   
   /**
    * Returns the currently selected node.
    * @return {@link Node} that is selected on the treeViewer
    */
   public Node getSelectedNode() {
      return treeViewer != null ? getNode(treeViewer.getSelection()) : null;
   }
   
   /**
    * Returns the currently selected node.
    * @return {@link Node} that is selected on the treeViewer
    */
   public Node getNode(ISelection selection) {
      Object selectedObj = SWTUtil.getFirstElement(selection);
      if (selectedObj instanceof Node) {
         return (Node) selectedObj;
      }
      else if (selectedObj instanceof BranchFolder) {
         return ((BranchFolder) selectedObj).getChild();
      }
      else {
         return null;
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
   public void addPropertyChangeListener(PropertyChangeListener listener) {
      pcs.addPropertyChangeListener(listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
      pcs.addPropertyChangeListener(propertyName, listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(PropertyChangeListener listener) {
      pcs.removePropertyChangeListener(listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
      pcs.removePropertyChangeListener(propertyName, listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PropertyChangeListener[] getPropertyChangeListeners() {
      return pcs.getPropertyChangeListeners();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
      return pcs.getPropertyChangeListeners(propertyName);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListeners() {
      return getPropertyChangeListeners().length >= 1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListeners(String propertyName) {
      return pcs.hasListeners(propertyName);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListener(PropertyChangeListener listener) {
      return ArrayUtil.contains(getPropertyChangeListeners(), listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListener(String propertyName, PropertyChangeListener listener) {
      return ArrayUtil.contains(getPropertyChangeListeners(propertyName), listener);
   }
}
