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
import org.key_project.keyide.ui.handlers.BreakpointToggleHandler;
import org.key_project.keyide.ui.handlers.HideIntermediateProofstepsHandler;
import org.key_project.keyide.ui.handlers.ShowSymbolicExecutionTreeOnlyHandler;
import org.key_project.keyide.ui.providers.BranchFolder;
import org.key_project.keyide.ui.providers.LazyProofTreeContentProvider;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.sed.key.core.model.IKeYSENode;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.ShowSubtreeOfNodeHandler;
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
   
   /**
    * the unique id of this view.
    */
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
    * the currently loaded {@link IProject}.
    */
   private IProject currentProject;
   
   /**
    * the currently selected node.
    */
   private Node selectedNode;
   
   /**
    * the flag indicating whether there is a new prof loaded or not.
    */
   private boolean newProof;
   
   /**
    * the flag indicating if a rule was manually applied or not.
    */
   private boolean isManualRule;
   
   /**
    * {@code true} if rule was applied manually and debugView is not updated yet, {@code false} otherwise.
    * Is needed so that selection is not updated twice after manual rule application.
    */
   private boolean beforeBaseViewUpdate;
   
   /**
	 * The {@link State} which indicates hiding or showing of intermediate proofsteps.
	 */
	private State hideState;
	
	/**
	 * the {@link State} for the show symbolic execution tree only outline filter.
	 */
	private State symbolicState;
   
	/**
	 * the {@link State} for stopping at breakpoints while auto mode is running. 
	 */
	private State breakpointState;
	
	/**
	 * the {@link State} for showing the subtree of a node.
	 */
	private State subtreeState;
	
	/**
	 * The root of the tree, changes after use of the show subtree of node filter.
	 */
	private Node filterNode;
	
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
    * the {@link IMenuListener} listening to actions on the context menu of the sourceViewer.
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
	 * the {@link IStateListener} to sync the show symbolic execution tree only toggleState with the outline page.
	 */
	private IStateListener symbolicStateListener = new IStateListener() {

      @Override
      public void handleStateChange(State state, Object oldValue) {
    	  handleSymbolicStateChanged(state, oldValue);
      }
	};
	
	/**
	 * the {@link IStateListener} to listen to changes on the breakpointState.
	 */
	private IStateListener breakpointStateListener = new IStateListener() {

      @Override
      public void handleStateChange(State state, Object oldValue) {
         handleBreakpointStateChanged(state, oldValue);
      }
	   
	};
	
	/**
	 * the {@link IStateListener} to listen to changes on the subtreeState.
	 */
	private IStateListener subtreeStateListener = new IStateListener() {

      @Override
      public void handleStateChange(State state, Object oldValue) {
         handleSubtreeStateChanged(state, oldValue);
         
      }
	   
	};
	

	/**
	 * the {@link KeYBreakpointManager} managing the available breakpoints.
	 */
	private KeYBreakpointManager breakpointManager;
	
	/**
	 * the {link RuleAppListener} listening to rule applications.
	 */
	private RuleAppListener ruleAppListener = new RuleAppListener() {
		
		@Override
		public void ruleApplied(ProofEvent e) {
			handleRuleApplied(e);
			
		}
	};

	/**
	 * the constructor of the class.
	 */
	public ManualView() {
	   
		ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
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
         
         Command breakpointCmd = service.getCommand(BreakpointToggleHandler.COMMAND_ID);
            if (breakpointCmd != null) {
               breakpointState = breakpointCmd.getState(RegistryToggleState.STATE_ID);
               if (breakpointState != null) {
                  breakpointState.addListener(breakpointStateListener);
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
      beforeBaseViewUpdate = false;
	   setManualRule(false);
	}
	
	/**
	 * handles the {@link ProofEvent} when a rule is applied manually. Updates selection.
	 * @param e the {@link ProofEvent} to handle
	 */
	protected void handleRuleApplied(ProofEvent e) {
	   
		if (!getProof().closed() && isManualRule) {
		   updateSelectedNodeThreadSafe();
			Iterator<Node> iterator = selectedNode.childrenIterator();
			Node newSelectedNode = selectedNode;
			while (iterator.hasNext()) {
				Node child = iterator.next();
				if (child.leaf()) {
					newSelectedNode = child;
				}
			}
			selectNodeThreadSafe(newSelectedNode);
			setManualRule(false);
			//don't listen to selection changes on baseView
			beforeBaseViewUpdate = true;
		}
		
	}

	/**
	 * sets the value of {@link ManualView#isManualRule}.
	 * @param b the boolean to set {@link ManualView#isManualRule} to
	 */
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
		if (selectedNode != null) {
		   selectNodeThreadSafe(selectedNode);
		}
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
		if (selectedNode != null) {
		   selectNodeThreadSafe(selectedNode);
		}
	}
   
	/**
	 * handles a change in breakpointState.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleBreakpointStateChanged(State state, Object oldValue) {
	   if (state.getValue() instanceof Boolean) {
	      breakpointManager.setEnabled((boolean) state.getValue());
	   } else {
	      breakpointManager.setEnabled(false);
	   }
	}
	
	/**
	 * handles the change in the subtreeState.
	 * @param state The state that has changed; never null. The value for this state has been updated to the new value.
	 * @param oldValue The old value; may be anything.
	 */
	protected void handleSubtreeStateChanged(State state, Object oldValue) {
	  if (proof != null) {
   	  if ((boolean) state.getValue()) {
   	     filterNode = getSelectedNode();
   	     contentProvider.setShowSubtreeState(true, filterNode);
   	     getTreeViewer().setInput(filterNode.proof());
   	  } else {
   	     Node selectedNode = getSelectedNode();
   	     contentProvider.setShowSubtreeState(false, proof.root());
   	     getTreeViewer().setInput(proof);
   	     if (!newProof && !(boolean) hideState.getValue()) {
   	        selectNodeThreadSafe(selectedNode);
   	     }
   	     filterNode = proof.root();
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
      this.treeViewer = new TreeViewer(parentComposite, SWT.SINGLE | SWT.H_SCROLL
            | SWT.V_SCROLL | SWT.VIRTUAL | SWT.BORDER);
      getTreeViewer().setUseHashlookup(true);
      this.contentProvider = new LazyProofTreeContentProvider();
      contentProvider.setHideState((boolean) hideState.getValue());
      contentProvider.setSymbolicState((boolean) symbolicState.getValue());
      subtreeState.setValue(false);
      getTreeViewer().setContentProvider(contentProvider);
      //create source viewer
      this.sourceViewer = new SourceViewer(parentComposite, null, SWT.MULTI | SWT.BORDER
            | SWT.FULL_SELECTION | SWT.H_SCROLL | SWT.V_SCROLL);
      getSourceViewer().setEditable(false);
      parentComposite.setWeights(new int[]{15, 85}); 
      parentComposite.setOrientation(SWT.HORIZONTAL);
      FormData data = new FormData();
      getSourceViewer().getControl().setLayoutData(data);
      sourceViewerDecorator = new ProofSourceViewerDecorator(getSourceViewer());
      getSite().setSelectionProvider(getTreeViewer());
      //update viewers if debugView is already open
      if (getProof() != null && environment != null && baseView != null) {
         updateViewer();
      }
      getSite().getPage().addSelectionListener(selectionListener);
   }
   
   /**
    * changes the currently shown proof if there is a selection change on the {@link DebugView}.
    * @param selection the current selection on {@link DebugView}
    */
   protected void handleSelectionChanged(ISelection selection) {
      //make sure that this is no update after manual rule application
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
                  //update only if selected target is not terminated
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
                     if (newProof) {
                        subtreeState.setValue(false);
                        contentProvider.setShowSubtreeState(false, proof.root());
                     }
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
                  //select associated node in the view
                  if (!(boolean) hideState.getValue()) {
                     IKeYSENode<?> seNode = (IKeYSENode<?>) element;
                     if (getTreeViewer() != null && getSourceViewer() != null) {
                        Node keyNode = seNode.getExecutionNode().getProofNode();
                        if (!(boolean) subtreeState.getValue()) {
                           selectNodeThreadSafe(keyNode);
                        } else if (keyNode.serialNr() >= filterNode.serialNr()) {
                           selectNodeThreadSafe(keyNode);
                        }
                     }
                  }
               }
            }
         }
         if (elements.length == 0 && getTreeViewer() != null && sourceViewerDecorator != null) {
            //if proof was removed after termination show nothing
            getTreeViewer().setInput(null);
            sourceViewerDecorator.showNode(null, null);
         }
      } else {
         //reset flag
         beforeBaseViewUpdate = false;
      }
   }

   
   /**
    * Updates the providers of {@link ManualView#getTreeViewer()} and {@link ManualView#getSourceViewer()}
    * and creates context menus. Selection is set to root.
    */
   protected void updateViewer() {
      Assert.isNotNull(getTreeViewer());
      Assert.isNotNull(getSourceViewer());
      Assert.isNotNull(sourceViewerDecorator);
      getTreeViewer().setInput(getProof());
      this.labelProvider = new ProofTreeLabelProvider(getTreeViewer(), environment.getProofControl(), getProof());
      getTreeViewer().setLabelProvider(labelProvider);
      contentProvider.injectTopLevelElements();
      //set default selection to root
//      if (!(boolean) subtreeState.getValue()) {
//         getTreeViewer().setSelection(SWTUtil.createSelection(getProof().root()), true);
//      } else {
//         getTreeViewer().setSelection(SWTUtil.createSelection(filterNode), true);
//      }
      createTreeViewerContextMenu();
      //set default selection to root
      if (!(boolean) hideState.getValue() || newProof) {
         if (!(boolean) subtreeState.getValue()) {
            selectNodeThreadSafe(proof.root());
         } else {
            selectNodeThreadSafe(filterNode);
         }
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
    * handles the {@link ProofEvent} when auto mode has stopped.
    * @param e the {@link ProofEvent} to handle
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      getSite().getPage().addSelectionListener(selectionListener);
      if (baseView != null) {
         baseView.getSite().getSelectionProvider().addSelectionChangedListener(baseViewListener);
     }
   }

   /**
    * handles the {@link ProofEvent} when auto mode has started.
    * @param e the {@link ProofEvent} to handle
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
    * the selection listener. Listens to changes on the treeViewer so that content of sourceViewer is the same.
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
   
   
   /**
    * method to make sure that a given {@link Node} is loaded. Is needed because of the filters.
    * @param node the {@link Node} to check
    */
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
			if (!contentProvider.getHideState() && !contentProvider.getSymbolicState() && !contentProvider.getShowSubtreeState()) {
				Assert.isTrue(viewIndex >= 0, "Content provider returned wrong parents or child index computation is buggy.");
				contentProvider.updateChildCount(parent, 0);
				contentProvider.updateElement(parent, viewIndex);
			} else if (viewIndex >= 0) {
				contentProvider.updateChildCount(parent, 0);
				contentProvider.updateElement(parent, viewIndex);
			}
		}
	}
   
	/**
	 * selects a given {@link Node}. 
	 * @param node the {@link Node} to select
	 */
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
    * method to select a node thread safe.
    * @param node the {@link Node} to select
    */
   protected void selectNodeThreadSafe(final Node node) {
	   
	   if (!treeViewer.getControl().getDisplay().isDisposed()) {
		   treeViewer.getControl().getDisplay().asyncExec(new Runnable() {
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
    * method to update local variable selectedNode thread safe.
    */
   private void updateSelectedNodeThreadSafe() {
      if (!treeViewer.getControl().getDisplay().isDisposed()) {
         treeViewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if (!treeViewer.getControl().isDisposed()) {
                  updateSelectedNode();
               }
            }
         });
      }
   }
   
   /**
    * updates local variable selectedNode.
    */
   private void updateSelectedNode() {
      if (getTreeViewer().getSelection() != null) {
         Object selection = SWTUtil.getFirstElement(getTreeViewer().getSelection());
         if (selection instanceof Node) {
            selectedNode = (Node) selection;
         } else if (selection instanceof BranchFolder) {
            selectedNode = ((BranchFolder) selection).getChild();
         } else {
            selectedNode = null;
         }
      } else {
         selectedNode = null;
      }
   }
   
   
   /**
    * returns the currently selected node.
    * @return {@link Node} that is selected on the treeViewer
    */
   public Node getSelectedNode() {
      updateSelectedNode();
      return this.selectedNode;
   }
   
   /**
    * returns the shown proof.
    * @return {@link Proof} that is opened.
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * returns the {@link TreeViewer}.
    * @return the {@link TreeViewer}
    */
   public TreeViewer getTreeViewer() {
      return treeViewer;
   }
   
   /**
    * returns the {@link SourceViewer}. 
    * @return the {@link SourceViewer}
    */
   public SourceViewer getSourceViewer() {
      return sourceViewer;
   }
   
   /**
    * returns the currently loaded {@link IProject}.
    * @return the {@link IProject}
    */
   public IProject getProject() {
      return currentProject;
   }
   
}
