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

package org.key_project.keyide.ui.views;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.util.SafeRunnable;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.part.IPageSite;
import org.eclipse.ui.part.Page;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.keyide.ui.composite.ProofTreeComposite;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.util.IProofNodeSearchSupport;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.core.KeYSelectionModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

/**
 * A class to display the correct Outline for the current {@link Proof}
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofTreeContentOutlinePage extends Page implements IContentOutlinePage, ISelectionChangedListener, ITabbedPropertySheetPageContributor, IProofNodeSearchSupport, IAdaptable {
   /**
    * The registered {@link ISelectionChangedListener}.
    */
   private final List<ISelectionChangedListener> selectionChangedListeners = new LinkedList<ISelectionChangedListener>();
   
   private final Proof proof;

	private final IProofProvider proofProvider;

	private final KeYSelectionModel selectionModel;
	
	/**
	 * The {@link ProofTreeComposite} which shows the proof tree.
	 */
	private ProofTreeComposite proofTreeComposite;
	
	/**
	 * {@link KeYSelectionListener} to sync the KeYSelection with the
	 * {@link TreeSelection}.
	 */
	private final KeYSelectionListener listener = new KeYSelectionListener() {
		@Override
		public void selectedProofChanged(KeYSelectionEvent e) {
			updateSelectedNodeThreadSafe();
		}

		@Override
		public void selectedNodeChanged(KeYSelectionEvent e) {
			if (e.getSource().getSelectedNode().proof() == proof) {
				updateSelectedNodeThreadSafe();
			}
		}
	};

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
	 * Constructor.
	 * @param proof The {@link Proof} for this Outline.
	 */
	public ProofTreeContentOutlinePage(Proof proof, 
	                                   IProofProvider proofProvider, 
	                                   KeYSelectionModel selectionModel) {
		this.proof = proof;
		this.proofProvider = proofProvider;
		this.selectionModel = selectionModel;
		selectionModel.addKeYSelectionListener(listener);
	}
	
	/**
	 * {@inheritDoc}
	 */
	@Override
   public void init(IPageSite pageSite) {
      super.init(pageSite);
      pageSite.setSelectionProvider(this);
   }

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void dispose() {
		selectionModel.removeKeYSelectionListener(listener);
		proofProvider.getProofControl().removeAutoModeListener(autoModeListener);
      if (proofTreeComposite != null) {
         proofTreeComposite.dispose();
      }
		super.dispose();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void createControl(Composite parent) {
      // Proof tree composite
      proofTreeComposite = new ProofTreeComposite(parent, SWT.NONE, SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL, proof, proofProvider.getEnvironment());
      proofTreeComposite.getTreeViewer().addSelectionChangedListener(this);
      proofProvider.getProofControl().addAutoModeListener(autoModeListener); // IMPORTANT: Needs to be registered after label provider is created. Otherwise, injecting elements during selection update fails.
		// Create context menu of TreeViewer
		MenuManager menuManager = new MenuManager("Outline popup", "org.key_project.keyide.ui.view.outline.popup");
		Menu menu = menuManager.createContextMenu(proofTreeComposite.getTreeViewer().getControl());
		proofTreeComposite.getTreeViewer().getControl().setMenu(menu);
		getSite().registerContextMenu("org.key_project.keyide.ui.view.outline.popup", menuManager, proofTreeComposite.getTreeViewer());
		updateSelectedNode();
	}

   /**
	 * When the auto mode starts.
	 * @param e The event.
	 */
	protected void handleAutoModeStarted(ProofEvent e) {
		// Ignore mediator selection changes while auto mode is running
		// (Behavior of original KeY UI and solves problem with selection
		// synchronization with the shown TreeViewer)
		selectionModel.removeKeYSelectionListener(listener);
	}

	/**
	 * When the auto mode stops.
	 * @param e The event.
	 */
	protected void handleAutoModeStopped(ProofEvent e) {
		if (e.getSource() == proof) {
			// Listen for mediator selection changes caused by the user to
			// synchronize them with the shown TreeViewer
			selectionModel.addKeYSelectionListener(listener);
			// Make sure that correct selected node is shown
			updateSelectedNodeThreadSafe();
		}
	}

	/**
	 * Executes {@link #updateSelectedNode()} asynchronously and thread safe.
	 */
	protected void updateSelectedNodeThreadSafe() {
		if (!getControl().isDisposed()) {
			getControl().getDisplay().asyncExec(new Runnable() {
				@Override
				public void run() {
					if (!getControl().isDisposed()) {
						updateSelectedNode();
					}
				}
			});
		}
	}

	/**
	 * Updates the selected node of the shown {@link TreeViewer} when the
	 * selection of the {@link KeYMediator} has changed.
	 */
	protected void updateSelectedNode() {
		Node mediatorNode = selectionModel.getSelectedNode();
		proofTreeComposite.selectNode(mediatorNode);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		// Change selected node of mediator only if content provider is not in
		// refresh phase after stopping the auto mode
		Node node = ProofTreeComposite.getSelectedNode(event.getSelection());
		Node mediatorNode = selectionModel.getSelectedNode();
		if (node != mediatorNode && node != null) {
			selectionModel.setSelectedNode(node);
		}
		// Fire event to listener
		fireSelectionChanged(event.getSelection());
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public String getContributorId() {
		return KeYEditor.CONTRIBUTOR_ID;
	}

	/**
	 * Returns the used {@link TreeViewer}.
	 * @return The used {@link TreeViewer} or {@code null} if not available.
	 */
   public TreeViewer getTreeViewer() {
      return proofTreeComposite != null ? proofTreeComposite.getTreeViewer() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISelection getSelection() {
      return proofTreeComposite != null ? proofTreeComposite.getSelection() : StructuredSelection.EMPTY;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setSelection(ISelection selection) {
      TreeViewer treeViewer = getTreeViewer();
      if (treeViewer != null) {
         treeViewer.setSelection(selection);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addSelectionChangedListener(ISelectionChangedListener listener) {
      if (listener != null) {
         selectionChangedListeners.add(listener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeSelectionChangedListener(ISelectionChangedListener listener) {
      if (listener != null) {
         selectionChangedListeners.remove(listener);
      }
   }
   
   /**
    * Returns all registered {@link ISelectionChangedListener}s.
    * @return All registered {@link ISelectionChangedListener}s.
    */
   public ISelectionChangedListener[] getSelectionChangedListeners() {
      return selectionChangedListeners.toArray(new ISelectionChangedListener[selectionChangedListeners.size()]);
   }
   
   /**
    * Fires a selection changed event.
    * @param selection the new selection
    */
   protected void fireSelectionChanged(ISelection selection) {
       // create an event
       final SelectionChangedEvent event = new SelectionChangedEvent(this, selection);
       // fire the event
       ISelectionChangedListener[] listeners = getSelectionChangedListeners();
       for (final ISelectionChangedListener l : listeners) {
           SafeRunner.run(new SafeRunnable() {
               public void run() {
                   l.selectionChanged(event);
               }
           });
       }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Control getControl() {
      return proofTreeComposite;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      TreeViewer treeViewer = getTreeViewer();
      if (treeViewer != null) {
         treeViewer.getControl().setFocus();
      }
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
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IProofProvider.class.equals(adapter)) {
         return proofProvider;
      }
      else {
         return Platform.getAdapterManager().getAdapter(this, adapter);
      }
   }
}