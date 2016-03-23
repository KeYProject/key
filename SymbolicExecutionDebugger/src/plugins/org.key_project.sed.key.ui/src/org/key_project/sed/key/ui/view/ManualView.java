package org.key_project.sed.key.ui.view;

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.key_project.key4eclipse.common.ui.breakpoints.KeYBreakpointManager;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.handlers.ShowSymbolicExecutionTreeOnlyHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * the view based on the {@link IDebugView} providing the possibility to apply rules manually.
 * @author Seena Vellaramkalayil
 *
 */
public class ManualView extends AbstractViewBasedView {
   
   public static final String VIEW_ID = "org.key_project.sed.key.ui.view.ManualView";
   
   /**
    * the {@link SashForm} to divide [@link TreeViewer} and {@link SourceViewer}.
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
    * the loaded {@link Proof}.
    */
   private Proof proof;

   /**
    * the {@link LazyProofTreeContentProvider} of the treeViewer.
    */
   private LazyProofTreeContentProvider contentProvider;

   /**
    * the {@link ProofTreeLabelProvider} of the treeViewer.
    */
   private ProofTreeLabelProvider labelProvider;

   /**
    * the {@link KeYEnvironment} of the proof.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * the {@link ProofSourceViewerDecorator} of the sourceViewer.
    */
   private ProofSourceViewerDecorator sourceViewerDecorator;
   
   /**
    * 
    */
   private IProject currentProject;
   
   /**
    * indicates whether there is a new prof loaded or not.
    */
   private boolean newProof;
   
   /**
    * {@code true} if rule was applied manually and debugView is not updated yet, {@code false} otherwise.
    */
   private boolean beforeBaseViewUpdate;
   
   /**
	 * The {@link State} which indicates hiding or showing of intermediate proofsteps.
	 */
	private State hideState;
	
	/**
	 * The {@link State} for the show symbolic execution tree only outline filter.
	 */
	private State symbolicState;
   
	/**
	 * The {@link State} for stopping at breakpoints while auto mode is running. 
	 */
	private State breakpointState;
	
   /**
    * the {@link ISelectionChangedListener} for the {@link IDebugView}.
    */
   private ISelectionChangedListener baseViewListener = new ISelectionChangedListener() {

      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleSelectionChanged(event.getSelection());
      }
   };
   
   /**
    * the {@link AutoModeListener}.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {

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
    * the {@link IMenuListener} listening actions on the context menu of the sourceViewer.
    */
   private IMenuListener contextMenuListener = new IMenuListener() {
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
	private IStateListener hideStateListener = new IStateListener() {

		@Override
		public void handleStateChange(State state, Object oldValue) {
			handleHideStateChanged(state, oldValue);
		}
	};
	
	/**
	 * The {@link IStateListener} to sync the show symbolic execution tree only toggleState with the outline page.
	 */
	private IStateListener symbolicStateListener = new IStateListener(){

      @Override
      public void handleStateChange(State state, Object oldValue) {
    	  handleSymbolicStateChanged(state, oldValue);
      }
	};
	
	/**
	 * The {@link IStateListener} to listen to changes on the breakpointState.
	 */
	private IStateListener breakpointStateListener = new IStateListener() {

      @Override
      public void handleStateChange(State state, Object oldValue) {
         handleBreakpointStateChanged(state, oldValue);
      }
	   
	};
	
	/**
	 * 
	 */
	private KeYBreakpointManager breakpointManager;
	
	private RuleAppListener ruleAppListener = new RuleAppListener() {
		
		@Override
		public void ruleApplied(ProofEvent e) {
			handleRuleApplied(e);
			
		}
	};

	private boolean isManualRule;

	
	public ManualView() {
	   
		ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
      if (service != null) {
         Command hideCmd = service.getCommand(HideIntermediateProofstepsHandler.COMMAND_ID);
         if (hideCmd != null) {
            hideState = hideCmd.getState(RegistryToggleState.STATE_ID);
            if (hideState != null) {
            	hideState.setValue(false); //TODO remove
            	hideState.addListener(hideStateListener);
            }
         }
         
         Command symbolicCmd = service.getCommand(ShowSymbolicExecutionTreeOnlyHandler.COMMAND_ID);
         if (symbolicCmd != null) {
            symbolicState = symbolicCmd.getState(RegistryToggleState.STATE_ID);
            if (symbolicState != null) {
            	symbolicState.setValue(false); //TODO remove
            	symbolicState.addListener(symbolicStateListener);
            }
         }
         
         Command breakpointCmd = service.getCommand(ShowSymbolicExecutionTreeOnlyHandler.COMMAND_ID);
         if (breakpointCmd != null) {
            if (hideCmd != null) {
               breakpointState = hideCmd.getState(RegistryToggleState.STATE_ID);
               if (breakpointState != null) {
                  breakpointState.addListener(breakpointStateListener);
               }
            }
         }
      }
      beforeBaseViewUpdate = false;
	      
	}
	
	protected void handleRuleApplied(ProofEvent e) {
		if (!getProof().closed() && isManualRule) {
			Node selectedNode = getSelectedNode();
			Iterator<Node> iterator = selectedNode.childrenIterator();
			Node newSelectedNode = selectedNode;
			while (iterator.hasNext()) {
				Node child = iterator.next();
				if (child.leaf()) {
					newSelectedNode = child;
				}
			}
			selectNode(newSelectedNode);
			setManualRule(false);
			//don't listen to selection changes on baseView
			beforeBaseViewUpdate = true;
		}
		
	}

	public void setManualRule(boolean b) {
		isManualRule = b;
	}

	/**
	 * Handles a change in the state of the hideIntermediateProofsteps outline filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleHideStateChanged(State state, Object oldValue) {
		Node selectedNode = getSelectedNode();
		contentProvider.setHideState((boolean) state.getValue());
		getTreeViewer().setInput(proof);
		selectNode(selectedNode);
	}
	
	/**
	 * Handles a change in the state of the showSymbolicExecutionTree outline filter.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleSymbolicStateChanged(State state, Object oldValue) {
		Node selectedNode = getSelectedNode();
		contentProvider.setSymbolicState((boolean) state.getValue());
		getTreeViewer().setInput(proof);
		selectNode(selectedNode);
	}
   
	/**
	 * 
	 */
	protected void handleBreakpointStateChanged(State state, Object oldValue) {
	   if (state.getValue() instanceof Boolean) {
	      breakpointManager.setEnabled((boolean) state.getValue());
	   } else {
	      breakpointManager.setEnabled(false);
	   }
	}
	
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      parentComposite = new SashForm(parent, SWT.HORIZONTAL);
      //create tree viewer
      this.treeViewer = new TreeViewer(parentComposite, SWT.SINGLE | SWT.H_SCROLL
            | SWT.V_SCROLL | SWT.VIRTUAL | SWT.BORDER);
      getTreeViewer().setUseHashlookup(true);
      this.contentProvider = new LazyProofTreeContentProvider();
      contentProvider.setHideState((boolean) hideState.getValue());
      contentProvider.setSymbolicState((boolean) symbolicState.getValue());
      getTreeViewer().setContentProvider(contentProvider);
      //create the source viewer
      this.sourceViewer = new SourceViewer(parentComposite, null, SWT.MULTI | SWT.BORDER
            | SWT.FULL_SELECTION | SWT.H_SCROLL | SWT.V_SCROLL);
      getSourceViewer().setEditable(false);
      parentComposite.setWeights(new int[]{15, 85});
      parentComposite.setOrientation(SWT.HORIZONTAL);
      FormData data = new FormData();
      getSourceViewer().getControl().setLayoutData(data);
      sourceViewerDecorator = new ProofSourceViewerDecorator(getSourceViewer());
      getSite().setSelectionProvider(getTreeViewer());
      if (getProof() != null && environment != null && baseView != null) {
         updateViewer();
      }
      getSite().getPage().addSelectionListener(selectionListener);
   }
   
   /**
    * changes the currently shown proof if there is a selection change on the {@link DebugView}.
    * @param selection
    */
   protected void handleSelectionChanged(ISelection selection) {
      if (!beforeBaseViewUpdate) {
         Assert.isNotNull(selection);
         Object[] elements = SWTUtil.toArray(selection);
         for (Object element: elements) {
            if (element instanceof ILaunch) {
               element = ((ILaunch) element).getDebugTarget();
            }
            if (element instanceof IDebugElement) {
               IDebugTarget target = ((IDebugElement) element).getDebugTarget();
               if (target instanceof KeYDebugTarget) {
                  KeYDebugTarget keyTarget = (KeYDebugTarget) target;
                  if (!keyTarget.isTerminated()) {
   	        	   if (getProof() != null && !getProof().isDisposed()) {
   	        	      getProof().removeRuleAppListener(ruleAppListener);
   	        	      DebugPlugin.getDefault().getBreakpointManager().removeBreakpointListener(breakpointManager);
   	        	      if (!getProof().equals(keyTarget.getProof())) {
   	        	         newProof = true;
   	        	      }
   	        	   } else {
   	        	      newProof = true;
   	        	   }
                  this.proof = keyTarget.getProof();
                  this.environment = keyTarget.getEnvironment();
                  if (keyTarget.getMethod() != null) {
                     this.currentProject = keyTarget.getMethod().getResource().getProject();
                  } else {
                     this.currentProject = null;
                  }
                  environment.getProofControl().setMinimizeInteraction(true);
                  if (getTreeViewer() != null && getSourceViewer() != null) {
                     updateViewer();
                  }
                  getProof().addRuleAppListener(ruleAppListener);
                  breakpointManager = new KeYBreakpointManager(getProof());
                  DebugPlugin.getDefault().getBreakpointManager().addBreakpointListener(breakpointManager);
                  } else {
                     proof = null;
                     environment = null;
                     return;
                  }
               }
               if (element instanceof IKeYSENode<?>) {
                  if (!(boolean) hideState.getValue()) {
                     IKeYSENode<?> seNode = (IKeYSENode<?>) element;
                     if (getTreeViewer() != null && getSourceViewer() != null) {
                        Node keyNode = seNode.getExecutionNode().getProofNode();
                        selectNode(keyNode);
                        sourceViewerDecorator.showNode(keyNode, SymbolicExecutionUtil.createNotationInfo(getProof()));
                     }
                  }
               }
            }
         }
         if (elements.length == 0 && getTreeViewer() != null && sourceViewerDecorator != null) {
            getTreeViewer().setInput(null);
            sourceViewerDecorator.showNode(null, null);
         }
      } else {
         beforeBaseViewUpdate = false;
      }
   }

   
   /**
    * updates the providers of the treeViewer and the sourceViewer.
    */
   protected void updateViewer() {
      Assert.isNotNull(getTreeViewer());
      Assert.isNotNull(getSourceViewer());
      Assert.isNotNull(sourceViewerDecorator);
      getTreeViewer().setInput(getProof());
      this.labelProvider = new ProofTreeLabelProvider(getTreeViewer(), environment.getProofControl(), getProof());
      getTreeViewer().setLabelProvider(labelProvider);
      contentProvider.injectTopLevelElements();
      
      getTreeViewer().setSelection(SWTUtil.createSelection(getProof().root()), true);
      createTreeViewerContextMenu();
      if (!(boolean) hideState.getValue() || newProof) {
         sourceViewerDecorator.showNode(getProof().root(), SymbolicExecutionUtil.createNotationInfo(getProof()));
         newProof = false;
      }
      getSourceViewer().getControl().setSize(1000,1000);
      createSourceViewerContextMenu();
   }
   
   /**
    * method to create the context menu shown on this view's tree viewer.
    */
   private void createTreeViewerContextMenu() {
      MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
      Menu menu = menuManager.createContextMenu(getTreeViewer().getControl());
      getTreeViewer().getControl().setMenu(menu);
      getSite().registerContextMenu("org.key_project.keyide.ui.view.outline.popup", menuManager, getTreeViewer());
   }
   
   /**
    * method to create the context menu containing the available rules to apply on the proof.
    */
   private void createSourceViewerContextMenu() {
      StyledText styledText = getSourceViewer().getTextWidget();
      MenuManager menuMgr = new MenuManager(getSourceViewerMenuId(), getSourceViewerMenuId());
      menuMgr.setRemoveAllWhenShown(true);
      menuMgr.addMenuListener(contextMenuListener);
      Menu menu = menuMgr.createContextMenu(styledText);
      styledText.setMenu(menu);
      getSite().registerContextMenu(getSourceViewerMenuId(), menuMgr, getSourceViewer());
   }

   /**
    * resets the input of the tree viewer after the auto mode has finished.
    * @param e
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      getSite().getPage().addSelectionListener(selectionListener);
      if (baseView != null) {
         baseView.getSite().getSelectionProvider().addSelectionChangedListener(baseViewListener);
     }
   }

   /**
    * removes all listeners so that they won't collide with the auto mode.
    * @param e
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (getProof() != null) {
         getSite().getPage().removeSelectionListener(selectionListener);
         baseView.getSite().getSelectionProvider().removeSelectionChangedListener(baseViewListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (parentComposite != null) {
         parentComposite.dispose();
      }
      if (getTreeViewer() != null) {
         getTreeViewer().getControl().dispose();
      }
      if (getSourceViewer() != null) {
         getSourceViewer().getControl().dispose();
      }
      if (environment != null) {
         environment.getProofControl().removeAutoModeListener(autoModeListener);
      }
      if (baseView != null) {
         baseView.getSite().getSelectionProvider().removeSelectionChangedListener(baseViewListener);
      }
      if (getProof() != null) {
    	  getProof().removeRuleAppListener(ruleAppListener);
      }
      if (hideState != null) {
    	  hideState.removeListener(hideStateListener);
      }
      if (symbolicState != null) {
    	  symbolicState.removeListener(symbolicStateListener);
      }	
      if (breakpointState != null) {
         breakpointState.removeListener(breakpointStateListener);
      }
      if (breakpointManager != null) {
         DebugPlugin.getDefault().getBreakpointManager().removeBreakpointListener(breakpointManager);
      }
      getSite().getPage().removeSelectionListener(selectionListener);
      
      super.dispose();
   }
   
   /**
    * returns the id of the context menu of the source viewer.
    * @return String id of the context menu
    */
   protected String getSourceViewerMenuId() {
      return "org.key_project.sed.key.ui.ManualView.popup";
   }

   
   /**
    * returns the {@link PosInSequent} that is currently selected.
    * @return {@link PosInSequent} the position in the sequent that is selected
    */
   public PosInSequent getSelectedPosInSequent() {
      return sourceViewerDecorator.getSelectedPosInSequent();
   }
   
   /**
    * returns the environment of the proof.
    * @return {@link KeYEnvironment<?>} the environment
    */
   public KeYEnvironment<?> getEnvironment() {
      return environment;
   }
   
   
   /**
    * the selection listener. Listens to changes on the treeViewer.
    */
   private final ISelectionListener selectionListener = new ISelectionListener() {

      @Override
      public void selectionChanged(IWorkbenchPart part, ISelection selection) {
         if (selection instanceof IStructuredSelection && part instanceof ManualView) {
            Object selectedObj = SWTUtil.getFirstElement(selection);
            if (selectedObj instanceof Node) {
               Node node = (Node) selectedObj;
               if (getProof().find(node)) {
                  sourceViewerDecorator.showNode(node, SymbolicExecutionUtil.createNotationInfo(getProof()));
               } 
            }  else if (selectedObj instanceof BranchFolder) {
               BranchFolder bf = (BranchFolder) selectedObj;
               Node node = bf.getChild();
               sourceViewerDecorator.showNode(node, SymbolicExecutionUtil.createNotationInfo(getProof()));
            }
         } 
         
      }
      
   };

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseViewReference(
         IViewReference baseViewReference) {
      if (IDebugUIConstants.ID_DEBUG_VIEW.equals(baseViewReference.getId())) {
         return true;
      }
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      if (IDebugUIConstants.ID_DEBUG_VIEW.equals(baseView.getSite().getId())) {
         return true;
      }
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView,
         IViewPart newBaseView) {
      if (oldBaseView != null) {
         oldBaseView.getSite().getSelectionProvider().removeSelectionChangedListener(baseViewListener);
      }
      if (newBaseView != null) {
         this.baseView = newBaseView;
         ISelectionProvider selectionProvider = baseView.getSite().getSelectionProvider();
         selectionProvider.addSelectionChangedListener(baseViewListener);
         handleSelectionChanged(selectionProvider.getSelection());
         
      }
   }
   
   protected void makeSureElementIsLoaded(Node node) {
	// Collect unknown parents
			Deque<Object> unknownParents = new LinkedList<Object>();
			boolean unknown = true;
			Object current = node;
			while (unknown && current != null) {
				if (getTreeViewer().testFindItem(current) == null) {
					unknownParents.addFirst(current);
				} else {
					unknown = false;
				}
				current = contentProvider.getParent(current);
			}
			// Inject unknown elements
			for (Object unknownElement : unknownParents) {
				Object parent = contentProvider.getParent(unknownElement);
				int viewIndex = contentProvider.getIndexOf(parent, unknownElement);
				if (contentProvider.getHideState() == false && contentProvider.getSymbolicState() == false) {
				   Assert.isTrue(viewIndex >= 0, "Content provider returned wrong parents or child index computation is buggy.");
				   contentProvider.updateChildCount(parent, 0);
				   contentProvider.updateElement(parent, viewIndex);
				} else if (viewIndex >= 0){
					contentProvider.updateChildCount(parent, 0);
					contentProvider.updateElement(parent, viewIndex);
				}
			}
   }
   
   protected void selectNode(Node node) {
	   makeSureElementIsLoaded(node);
	   
	   Object parent = contentProvider.getParent(node);
	   int viewIndex = contentProvider.getIndexOf(parent, node);
	   
	   if (viewIndex >= 0) {
		   getTreeViewer().setSelection(SWTUtil.createSelection(node), true);
		   sourceViewerDecorator.showNode(node, SymbolicExecutionUtil.createNotationInfo(proof));
	   } else {
		   getTreeViewer().setSelection(SWTUtil.createSelection(parent), true);
		   if (parent instanceof Node) {
		      sourceViewerDecorator.showNode((Node) parent, SymbolicExecutionUtil.createNotationInfo(proof));
		   } else if (parent instanceof BranchFolder) {
		      sourceViewerDecorator.showNode(((BranchFolder) parent).getChild(), SymbolicExecutionUtil.createNotationInfo(proof));
		   }
	   }
   }
   
   /**
    * returns the currently selected node.
    * @return {@link Node} that is selected on the treeViewer
    */
   public Node getSelectedNode() {
      if (getTreeViewer().getSelection() != null) {
         Object selection = SWTUtil.getFirstElement(getTreeViewer().getSelection());
         if (selection instanceof Node) {
            Node selectedNode = (Node) selection;
            return selectedNode;
         } else if (selection instanceof BranchFolder) {
        	 Node selectedNode = ((BranchFolder) selection).getChild();
        	 return selectedNode;
         }
         return null;
      }
      return null;
   }
   
   /**
    * returns the shown proof.
    * @return {@link Proof} that is opened.
    */
   public Proof getProof() {
      return proof;
   }

   public TreeViewer getTreeViewer() {
      return treeViewer;
   }
   
   public SourceViewer getSourceViewer() {
      return sourceViewer;
   }
   
   public IProject getProject() {
      return currentProject;
   }
   
}
