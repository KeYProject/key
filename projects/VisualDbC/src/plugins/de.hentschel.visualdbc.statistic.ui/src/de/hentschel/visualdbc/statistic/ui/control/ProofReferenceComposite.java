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

package de.hentschel.visualdbc.statistic.ui.control;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.common.notify.impl.AdapterImpl;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.provider.ComposedAdapterFactory;
import org.eclipse.emf.edit.provider.ReflectiveItemProviderAdapterFactory;
import org.eclipse.emf.edit.provider.resource.ResourceItemProviderAdapterFactory;
import org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider;
import org.eclipse.jface.layout.TreeColumnLayout;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcOperation;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.dbcmodel.provider.DbcmodelItemProviderAdapterFactory;

/**
 * Shows the proof references of selected elements provided by an {@link IProofReferenceProvider}.
 * @author Martin Hentschel
 */
public class ProofReferenceComposite extends Composite {
   /**
    * The {@link IEditorPart} which provides the content.
    */
   private IEditorPart editor;
   
   /**
    * The {@link IProofReferenceProvider} to use.
    */
   private IProofReferenceProvider proofReferenceProvider;
   
   /**
    * Shows the available proof references.
    */
   private TreeViewer viewer;

   /**
    * The used {@link ITreeContentProvider} in {@link #viewer}.
    */
   private ProofReferenceTreeContentProvider contentProvider;
   
   /**
    * The used {@link ITableLabelProvider} in {@link #viewer}.
    */
   private ProofReferenceLabelProvider labelProvider;
   
   /**
    * Listens for selection changes on {@link #editor}.
    */
   private ISelectionChangedListener selectionListener = new ISelectionChangedListener() {
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         handleSelectionChanged(event);
      }
   };
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param editor The {@link IEditorPart} which provides the content.
    * @param proofReferenceProvider The {@link IProofReferenceProvider} to use.
    */
   public ProofReferenceComposite(Composite parent, int style, IEditorPart editor, IProofReferenceProvider proofReferenceProvider) {
      super(parent, style);
      Assert.isNotNull(editor);
      Assert.isNotNull(proofReferenceProvider);
      this.editor = editor;
      this.proofReferenceProvider = proofReferenceProvider;
      editor.getEditorSite().getSelectionProvider().addSelectionChangedListener(selectionListener);
      // Create viewer
      TreeColumnLayout viewerLayout = new TreeColumnLayout();
      setLayout(viewerLayout);
      viewer = new TreeViewer(this, SWT.BORDER | SWT.H_SCROLL | SWT.V_SCROLL | SWT.MULTI | SWT.FULL_SELECTION);
      viewer.getTree().setHeaderVisible(true);
      viewer.getTree().setLinesVisible(true);
      viewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      // Add main column
      TreeViewerColumn mainColumn = new TreeViewerColumn(viewer, SWT.NONE);
      mainColumn.getColumn().setText("Selected Element");
      mainColumn.getColumn().setMoveable(true);
      viewerLayout.setColumnData(mainColumn.getColumn(), new ColumnWeightData(40));
      // Add direction column
      TreeViewerColumn directionColumn = new TreeViewerColumn(viewer, SWT.NONE);
      directionColumn.getColumn().setText("Direction");
      directionColumn.getColumn().setMoveable(true);
      viewerLayout.setColumnData(directionColumn.getColumn(), new ColumnWeightData(10));
      // Add kind column
      TreeViewerColumn kindColumn = new TreeViewerColumn(viewer, SWT.NONE);
      kindColumn.getColumn().setText("Kind");
      kindColumn.getColumn().setMoveable(true);
      viewerLayout.setColumnData(kindColumn.getColumn(), new ColumnWeightData(20));
      // Add direction target column
      TreeViewerColumn directionTargetColumn = new TreeViewerColumn(viewer, SWT.NONE);
      directionTargetColumn.getColumn().setText("Direction Target");
      directionTargetColumn.getColumn().setMoveable(true);
      viewerLayout.setColumnData(directionTargetColumn.getColumn(), new ColumnWeightData(40));
      // Update content in viewer
      updateContent(editor.getEditorSite().getSelectionProvider().getSelection());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      editor.getEditorSite().getSelectionProvider().removeSelectionChangedListener(selectionListener);
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();         
      }
      super.dispose();
   }

   /**
    * Handles a double click in the viewer.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      if (proofReferenceProvider != null) {
         List<?> selectedElements = SWTUtil.toList(event.getSelection());
         List<Object> toSelect = new LinkedList<Object>();
         for (Object selected : selectedElements) {
            if (selected instanceof ProofReferenceEntry) {
               toSelect.add(((ProofReferenceEntry)selected).getDirectionTarget());
            }
            else {
               toSelect.add(selected);
            }
         }
         proofReferenceProvider.select(toSelect);
      }
   }
   
   /**
    * When the selection of {@link #editor} has changed.
    * @param event The event.
    */
   protected void handleSelectionChanged(SelectionChangedEvent event) {
      updateContent(event.getSelection());
   }
   
   /**
    * Sets the input of {@link #viewer}.
    * @param selection The {@link ISelection} to show in {@link #viewer}.
    */
   protected void updateContent(ISelection selection) {
      // Add new provider to remove no longer needed observed objects
      if (contentProvider != null) {
         contentProvider.dispose();
      }
      contentProvider = new ProofReferenceTreeContentProvider();
      viewer.setContentProvider(contentProvider);
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      labelProvider = new ProofReferenceLabelProvider();
      viewer.setLabelProvider(labelProvider);
      // Set new input
      List<?> elements = SWTUtil.toList(selection);
      List<?> elementsToShow = proofReferenceProvider.extractElementsToShow(elements);
      if (elementsToShow == null) {
         elementsToShow = Collections.emptyList();
      }
      viewer.setInput(elementsToShow);
      viewer.expandToLevel(2);
   }

   /**
    * The {@link ITreeContentProvider} used in the viewer of {@link ProofReferenceComposite}.
    * @author Martin Hentschel
    */
   public static class ProofReferenceTreeContentProvider implements ITreeContentProvider {
      /**
       * The {@link TreeViewer} in which this {@link ITreeContentProvider} is used.
       */
      private TreeViewer viewer;
      
      /**
       * The current input of {@link #viewer}.
       */
      private Object input;
      
      /**
       * The filtered elements of {@link #input} which are shown in {@link #viewer}.
       */
      private Set<EObject> filteredInput;
      
      /**
       * Observed {@link EObject}s.
       */
      private Set<EObject> observedObjects = new HashSet<EObject>();
      
      /**
       * Listener on each instance in {@link #observedObjects}.
       */
      private Adapter changeListener = new AdapterImpl() {
         @Override
         public void notifyChanged(Notification msg) {
            handleNotifyChanged(msg);
         }
      };
      
      /**
       * Mapping of a parent element to its children.
       */
      private Map<Object, Object[]> childMapping = new HashMap<Object, Object[]>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
         clearObservedObjects();
         this.childMapping.clear();
         this.viewer = viewer instanceof TreeViewer ? (TreeViewer)viewer : null;
         this.input = newInput;
         this.filteredInput = filterInput(newInput);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         clearObservedObjects();
         this.childMapping.clear();
      }
      
      /**
       * Removes the change listener from all objects in {@link #observedObjects}
       * and clears the list.
       */
      protected void clearObservedObjects() {
         for (EObject obj : observedObjects) {
            obj.eAdapters().remove(changeListener);
         }
         observedObjects.clear();
      }
      
      /**
       * Adds the change listener {@link #changeListener} to the given {@link EObject}
       * and registers the {@link EObject} in {@link #observedObjects}.
       * @param obj The {@link EObject} to observe.
       */
      protected void observeObject(EObject obj) {
         if (observedObjects.add(obj)) {
            obj.eAdapters().add(changeListener);
         }
      }

      /**
       * When something has changed on an observed {@link EObject} in {@link #observedObjects}.
       * @param msg The event.
       */
      protected void handleNotifyChanged(Notification msg) {
         if (DbcmodelPackage.Literals.DBC_PROOF_REFERENCE__SOURCE.equals(msg.getFeature()) ||
             DbcmodelPackage.Literals.DBC_PROOF_REFERENCE__TARGET.equals(msg.getFeature()) ||
             DbcmodelPackage.Literals.DBC_PROOF__PROOF_REFERENCES.equals(msg.getFeature()) ||
             DbcmodelPackage.Literals.IDB_CPROOF_REFERENCABLE__ALL_REFERENCES.equals(msg.getFeature())) {
            updateChildren(msg.getNotifier());
            if (msg.getNewValue() instanceof DbcProofReference) {
               DbcProofReference reference = (DbcProofReference)msg.getNewValue();
               updateChildren(reference.getSource());
               updateChildren(reference.getTarget());
            }
            if (msg.getOldValue() instanceof DbcProofReference) {
               DbcProofReference reference = (DbcProofReference)msg.getOldValue();
               updateChildren(reference.getSource());
               updateChildren(reference.getTarget());
            }
         }
      }
      
      /**
       * Updates the children of the given parent element in {@link #viewer}.
       * @param parentElement The parent element to update its children.
       */
      protected void updateChildren(final Object parentElement) {
         if (parentElement != null && viewer != null && !viewer.getControl().isDisposed()) {
            viewer.getControl().getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  if (viewer.getControl().isDisposed()) {
                     Object[] children = childMapping.remove(parentElement);
                     if (children != null) {
                        viewer.remove(parentElement, children);
                     }
                     viewer.add(parentElement, getChildren(parentElement));
                  }
               }
            });
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object[] getChildren(Object parentElement) {
         Object[] children = childMapping.get(parentElement);
         if (children == null) {
            if (parentElement == input) {
               children = filteredInput.toArray(new Object[filteredInput.size()]);
            }
            else if (parentElement instanceof DbcProof) {
               DbcProof proof = (DbcProof)parentElement;
               observeObject(proof);
               List<DbcProofReference> references = proof.getProofReferences();
               List<Object> result = new LinkedList<Object>();
               for (DbcProofReference reference : references) {
                  result.add(new ProofReferenceEntry(proof, reference, "outgoing", reference.getTarget()));
               }
               children = result.toArray(new Object[result.size()]);
            }
            else if (parentElement instanceof IDbCProofReferencable) {
               IDbCProofReferencable referencable = (IDbCProofReferencable)parentElement;
               observeObject(referencable);
               List<DbcProofReference> references = referencable.getAllReferences();
               List<Object> result = new LinkedList<Object>();
               for (DbcProofReference reference : references) {
                  result.add(new ProofReferenceEntry(referencable, reference, "incoming", reference.getSource()));
               }
               children = result.toArray(new Object[result.size()]);
            }
            else if (parentElement instanceof DbcProofReference) {
               DbcProofReference reference = (DbcProofReference)parentElement;
               observeObject(reference);
               children = new Object[] {new ProofReferenceEntry(reference, reference, "refers from", reference.getSource()),
                                        new ProofReferenceEntry(reference, reference, "refers to", reference.getTarget())};
            }
            else if (parentElement instanceof ProofReferenceEntry) {
               children = getChildren(((ProofReferenceEntry)parentElement).getDirectionTarget());
            }
            else {
               children = new Object[0];
            }
            childMapping.put(parentElement, children);
         }
         return children;
      }
      
      /**
       * Filters out the element from the given {@link Object} which
       * have nothing to do with proof references or the elements
       * which provides currently no proof references.
       * @param input The input.
       * @return The elements which have something to do with proof references.
       */
      protected Set<EObject> filterInput(Object input) {
         Set<EObject> filteredInput = new LinkedHashSet<EObject>();
         if (input instanceof List<?>) {
            List<?> inputList = (List<?>)input;
            for (Object element : inputList) {
               if (element instanceof DbcProof) {
                  DbcProof proof = (DbcProof)element;
                  if (!proof.getProofReferences().isEmpty()) {
                     filteredInput.add(proof);
                  }
               }
               else if (element instanceof IDbCProofReferencable) {
                  IDbCProofReferencable referencable = (IDbCProofReferencable)element;
                  if (!referencable.getAllReferences().isEmpty()) {
                     filteredInput.add(referencable);
                  }
               }
               else if (element instanceof DbcProofReference) {
                  filteredInput.add((EObject)element);
               }
            }
         }
         return filteredInput;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object getParent(Object element) {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean hasChildren(Object element) {
         return getChildren(element).length >= 1;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object[] getElements(Object inputElement) {
         return getChildren(inputElement);
      }
   }
   
   /**
    * A utility class which is instantiated from {@link ProofReferenceTreeContentProvider}
    * to represent a tree row entry with a direction.
    * @author Martin Hentschel
    */
   public static class ProofReferenceEntry {
      /**
       * The parent {@link Object} in the tree.
       */
      private Object parent;
      
      /**
       * The {@link DbcProofReference} which is the reason for this entry.
       */
      private DbcProofReference reference;
      
      /**
       * The direction.
       */
      private String direction;

      /**
       * The target of the direction.
       */
      private EObject directionTarget;
      
      /**
       * Constructor.
       * @param parent The parent {@link Object} in the tree.
       * @param reference The {@link DbcProofReference} which is the reason for this entry.
       * @param direction The direction.
       * @param directionTarget The target of the direction.
       */
      public ProofReferenceEntry(Object parent, DbcProofReference reference, String direction, EObject directionTarget) {
         this.parent = parent;
         this.reference = reference;
         this.direction = direction;
         this.directionTarget = directionTarget;
      }

      /**
       * Returns the parent {@link Object} in the tree.
       * @return The parent {@link Object} in the tree.
       */
      public Object getParent() {
         return parent;
      }

      /**
       * Returns the {@link DbcProofReference} which is the reason for this entry.
       * @return The {@link DbcProofReference} which is the reason for this entry.
       */
      public DbcProofReference getReference() {
         return reference;
      }

      /**
       * Returns the direction.
       * @return The direction.
       */
      public String getDirection() {
         return direction;
      }

      /**
       * Returns the target of the direction.
       * @return The target of the direction.
       */
      public EObject getDirectionTarget() {
         return directionTarget;
      }
   }
   
   /**
    * The {@link ITableLabelProvider} used in the viewer of {@link ProofReferenceComposite}.
    * @author Martin Hentschel
    */
   public static class ProofReferenceLabelProvider extends LabelProvider implements ITableLabelProvider {
      /**
       * Factory which has created {@link #childLabelProvider}.
       */
      private ComposedAdapterFactory adapterFactory;
      
      /**
       * A child {@link ILabelProvider} which is used to compute column images
       * and to detect when something has changed.
       */
      private AdapterFactoryLabelProvider childLabelProvider;

      /**
       * Listens for changes on {@link #childLabelProvider}.
       */
      private ILabelProviderListener childLabelProviderListener = new ILabelProviderListener() {
         @Override
         public void labelProviderChanged(LabelProviderChangedEvent event) {
            handleChildLabelProviderChanged(event);
         }
      };
      
      /**
       * Observed {@link EObject}s.
       */
      private Set<EObject> observedObjects = new HashSet<EObject>();
      
      /**
       * Listener on each instance in {@link #observedObjects}.
       */
      private Adapter changeListener = new AdapterImpl() {
         @Override
         public void notifyChanged(Notification msg) {
            handleNotifyChanged(msg);
         }
      };
      
      /**
       * Constructor.
       */
      public ProofReferenceLabelProvider() {
         adapterFactory = new ComposedAdapterFactory(ComposedAdapterFactory.Descriptor.Registry.INSTANCE);
         adapterFactory.addAdapterFactory(new ResourceItemProviderAdapterFactory());
         adapterFactory.addAdapterFactory(new DbcmodelItemProviderAdapterFactory());
         adapterFactory.addAdapterFactory(new ReflectiveItemProviderAdapterFactory());
         childLabelProvider = new AdapterFactoryLabelProvider(adapterFactory);
         childLabelProvider.setFireLabelUpdateNotifications(true);
         childLabelProvider.addListener(childLabelProviderListener);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         clearObservedObjects();
         childLabelProvider.removeListener(childLabelProviderListener);
         childLabelProvider.dispose();
         adapterFactory.dispose();
         super.dispose();
      }
      
      /**
       * Removes the change listener from all objects in {@link #observedObjects}
       * and clears the list.
       */
      protected void clearObservedObjects() {
         for (EObject obj : observedObjects) {
            obj.eAdapters().remove(changeListener);
         }
         observedObjects.clear();
      }
      
      /**
       * Adds the change listener {@link #changeListener} to the given {@link EObject}
       * and registers the {@link EObject} in {@link #observedObjects}.
       * @param obj The {@link EObject} to observe.
       */
      protected void observeObject(EObject obj) {
         if (observedObjects.add(obj)) {
            obj.eAdapters().add(changeListener);
         }
      }

      /**
       * When something has changed on an observed {@link EObject} in {@link #observedObjects}.
       * @param msg The event.
       */
      protected void handleNotifyChanged(Notification msg) {
         if (DbcmodelPackage.Literals.DBC_PROOF_REFERENCE__KIND.equals(msg.getFeature())) {
            fireLabelProviderChangedThreadSave(new LabelProviderChangedEvent(this));
         }
      }
      
      /**
       * When something has changed on {@link #childLabelProvider}.
       * @param event The event.
       */
      protected void handleChildLabelProviderChanged(LabelProviderChangedEvent event) {
         fireLabelProviderChangedThreadSave(new LabelProviderChangedEvent(this));
      }
      
      /**
       * Fires the event to all listeners thread save.
       * @param event The event to fire.
       */
      protected void fireLabelProviderChangedThreadSave(final LabelProviderChangedEvent event) {
         Display.getDefault().syncExec(new Runnable() {
            @Override
            public void run() {
               fireLabelProviderChanged(event);
            }
         });
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Image getColumnImage(Object element, int columnIndex) {
         if (element instanceof ProofReferenceEntry) {
            if (columnIndex == 0) {
               element = ((ProofReferenceEntry)element).getParent();
               return childLabelProvider.getImage(element);
            }
            else if (columnIndex == 3) {
               element = ((ProofReferenceEntry)element).getDirectionTarget();
               return childLabelProvider.getImage(element);
            }
            else {
               return null;
            }
         }
         else {
            if (columnIndex == 0) {
               return childLabelProvider.getImage(element);
            }
            else {
               return null;
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getColumnText(Object element, int columnIndex) {
         return getColumnText(element, columnIndex, true);
      }

      /**
       * Returns the column text to show.
       * @param element The element.
       * @param columnIndex The column index.
       * @param rootElement Is root element? 
       * @return The column text to show.
       */
      protected String getColumnText(Object element, int columnIndex, boolean rootElement) {
         if (element instanceof DbcProof) {
            if (columnIndex == 0 || columnIndex == 3 && !rootElement) {
               DbcProof proof = ((DbcProof)element);
               IDbCProvable target = proof.getTarget();
               return target != null ?
                      proof.getObligation() + " of " + getColumnText(target, 0) :
                      proof.getObligation();
            }
            else {
               return null;
            }
         }
         else if (element instanceof DbcProofReference) {
            if (columnIndex == 0) {
               DbcProofReference reference = ((DbcProofReference)element);
               observeObject(reference);
               return reference.getKind();
            }
            else {
               return null;
            }
         }
         else if (element instanceof IDbCProofReferencable) {
            if (columnIndex == 0 || columnIndex == 3 && !rootElement) {
               if (element instanceof DbcAttribute) {
                  return ((DbcAttribute)element).getName();
               }
               else if (element instanceof DbcAxiom) {
                  return ((DbcAxiom)element).getName();
               }
               else if (element instanceof DbcEnumLiteral) {
                  return ((DbcEnumLiteral)element).getName();
               }
               else if (element instanceof DbcInvariant) {
                  return ((DbcInvariant)element).getName();
               }
               else if (element instanceof AbstractDbcOperation) {
                  return ((AbstractDbcOperation)element).getSignature();
               }
               else if (element instanceof AbstractDbcType) {
                  return ((AbstractDbcType)element).getName();
               }
               else if (element instanceof DbCAxiomContract) {
                  return ((DbCAxiomContract)element).getName();
               }
               else if (element instanceof DbcOperationContract) {
                  return ((DbcOperationContract)element).getName();
               }
               else {
                  return ObjectUtil.toString(element);
               }
            }
            else {
               return null;
            }
         }
         else if (element instanceof ProofReferenceEntry) {
            ProofReferenceEntry refEntry = (ProofReferenceEntry)element;
            if (columnIndex == 0) {
               return getColumnText(refEntry.getParent(), columnIndex, false);
            }
            else if (columnIndex == 1) {
               return refEntry.getDirection();
            }
            else if (columnIndex == 2) {
               observeObject(refEntry.getReference());
               return refEntry.getReference().getKind();
            }
            else if (columnIndex == 3) {
               return getColumnText(refEntry.getDirectionTarget(), columnIndex, false);
            }
            else {
               return null;
            }
         }
         else {
            return ObjectUtil.toString(element);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Image getImage(Object element) {
         return getColumnImage(element, 0);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getText(Object element) {
         return getColumnText(element, 0);
      }
   }
}