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

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.edit.domain.AdapterFactoryEditingDomain;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.emf.workspace.util.WorkspaceSynchronizer;
import org.eclipse.gmf.runtime.emf.core.GMFEditingDomainFactory;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.Node;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.ICommonContentProvider;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.AbstractDbcClassImplementsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomDbcAxiomCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassAttributeCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassAttributeCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorDbcConstructorCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumAttributeCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumAttributeCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumLiteralCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumLiteralCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceAttributeCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceAttributeCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodDbcMethodCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackage2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofTargetEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.part.Messages;

/**
 * @generated
 */
public class DbCNavigatorContentProvider implements ICommonContentProvider {

   /**
    * @generated
    */
   private static final Object[] EMPTY_ARRAY = new Object[0];

   /**
    * @generated
    */
   private Viewer myViewer;

   /**
    * @generated
    */
   private AdapterFactoryEditingDomain myEditingDomain;

   /**
    * @generated
    */
   private WorkspaceSynchronizer myWorkspaceSynchronizer;

   /**
    * @generated
    */
   private Runnable myViewerRefreshRunnable;

   /**
    * @generated
    */
   @SuppressWarnings({ "unchecked", "serial", "rawtypes" })
   public DbCNavigatorContentProvider() {
      TransactionalEditingDomain editingDomain = GMFEditingDomainFactory.INSTANCE
            .createEditingDomain();
      myEditingDomain = (AdapterFactoryEditingDomain) editingDomain;
      myEditingDomain.setResourceToReadOnlyMap(new HashMap() {
         public Object get(Object key) {
            if (!containsKey(key)) {
               put(key, Boolean.TRUE);
            }
            return super.get(key);
         }
      });
      myViewerRefreshRunnable = new Runnable() {
         public void run() {
            if (myViewer != null) {
               myViewer.refresh();
            }
         }
      };
      myWorkspaceSynchronizer = new WorkspaceSynchronizer(editingDomain,
            new WorkspaceSynchronizer.Delegate() {
               public void dispose() {
               }

               public boolean handleResourceChanged(final Resource resource) {
                  unloadAllResources();
                  asyncRefresh();
                  return true;
               }

               public boolean handleResourceDeleted(Resource resource) {
                  unloadAllResources();
                  asyncRefresh();
                  return true;
               }

               public boolean handleResourceMoved(Resource resource,
                     final URI newURI) {
                  unloadAllResources();
                  asyncRefresh();
                  return true;
               }
            });
   }

   /**
    * @generated
    */
   public void dispose() {
      myWorkspaceSynchronizer.dispose();
      myWorkspaceSynchronizer = null;
      myViewerRefreshRunnable = null;
      myViewer = null;
      unloadAllResources();
      ((TransactionalEditingDomain) myEditingDomain).dispose();
      myEditingDomain = null;
   }

   /**
    * @generated
    */
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      myViewer = viewer;
   }

   /**
    * @generated
    */
   void unloadAllResources() {
      for (Resource nextResource : myEditingDomain.getResourceSet()
            .getResources()) {
         nextResource.unload();
      }
   }

   /**
    * @generated
    */
   void asyncRefresh() {
      if (myViewer != null && !myViewer.getControl().isDisposed()) {
         myViewer.getControl().getDisplay().asyncExec(myViewerRefreshRunnable);
      }
   }

   /**
    * @generated
    */
   public Object[] getElements(Object inputElement) {
      return getChildren(inputElement);
   }

   /**
    * @generated
    */
   public void restoreState(IMemento aMemento) {
   }

   /**
    * @generated
    */
   public void saveState(IMemento aMemento) {
   }

   /**
    * @generated
    */
   public void init(ICommonContentExtensionSite aConfig) {
   }

   /**
    * @generated
    */
   public Object[] getChildren(Object parentElement) {
      if (parentElement instanceof IFile) {
         IFile file = (IFile) parentElement;
         URI fileURI = URI.createPlatformResourceURI(file.getFullPath()
               .toString(), true);
         Resource resource = myEditingDomain.getResourceSet().getResource(
               fileURI, true);
         ArrayList<DbCNavigatorItem> result = new ArrayList<DbCNavigatorItem>();
         ArrayList<View> topViews = new ArrayList<View>(resource.getContents()
               .size());
         for (EObject o : resource.getContents()) {
            if (o instanceof View) {
               topViews.add((View) o);
            }
         }
         return result.toArray();
      }

      if (parentElement instanceof DbCNavigatorGroup) {
         DbCNavigatorGroup group = (DbCNavigatorGroup) parentElement;
         return group.getChildren();
      }

      if (parentElement instanceof DbCNavigatorItem) {
         DbCNavigatorItem navigatorItem = (DbCNavigatorItem) parentElement;
         if (navigatorItem.isLeaf() || !isOwnView(navigatorItem.getView())) {
            return EMPTY_ARRAY;
         }
         return getViewChildren(navigatorItem.getView(), parentElement);
      }

      return EMPTY_ARRAY;
   }

   /**
    * @generated
    */
   private Object[] getViewChildren(View view, Object parentElement) {
      switch (DbCVisualIDRegistry.getVisualID(view)) {

      case DbcPackage2EditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcPackage2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         return result.toArray();
      }

      case DbcInterfaceEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInterface_2011_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInterface_2011_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceExtendsEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceExtendsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcProofTargetEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Edge sv = (Edge) view;
         DbCNavigatorGroup target = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcProofTarget_4001_target,
               "icons/linkTargetNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup source = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcProofTarget_4001_source,
               "icons/linkSourceNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnumEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcOperationContractEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcConstructorEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbCAxiomContractEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofEditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         if (!target.isEmpty()) {
            result.add(target);
         }
         if (!source.isEmpty()) {
            result.add(source);
         }
         return result.toArray();
      }

      case DbcEnumEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcEnum_2013_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcEnum_2013_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcConstructorEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnumLiteralEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcEnumLiteralEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcEnumLiteral_3020_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcClassExtendsEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Edge sv = (Edge) view;
         DbCNavigatorGroup target = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcClassExtends_4003_target,
               "icons/linkTargetNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup source = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcClassExtends_4003_source,
               "icons/linkSourceNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         if (!target.isEmpty()) {
            result.add(target);
         }
         if (!source.isEmpty()) {
            result.add(source);
         }
         return result.toArray();
      }

      case DbcOperationContractEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcOperationContract_3026_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcAttributeEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcAttribute_3011_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcInvariantEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInvariant_3035_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcProofEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcProof_2014_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcAxiomEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcAxiom_3036_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbCAxiomContractEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcClass2EditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcClass_3031_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcClass_3031_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcConstructorEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassExtendsEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassExtendsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcInterface2EditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInterface_3032_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInterface_3032_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceExtendsEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceExtendsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcConstructorEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcConstructor_3010_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry
                     .getType(DbcOperationContractEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcClassEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcClass_2012_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcClass_2012_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcConstructorEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassExtendsEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassExtendsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcProof2EditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcProof_3034_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbcEnum2EditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcEnum_3033_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup outgoinglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcEnum_3033_outgoinglinks,
               "icons/outgoingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcConstructorEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnumLiteralEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getOutgoingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         outgoinglinks.addChildren(createNavigatorItems(connectedViews,
               outgoinglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         if (!outgoinglinks.isEmpty()) {
            result.add(outgoinglinks);
         }
         return result.toArray();
      }

      case DbCAxiomContractEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbCAxiomContract_3037_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }

      case DbcInterfaceExtendsEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Edge sv = (Edge) view;
         DbCNavigatorGroup target = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInterfaceExtends_4004_target,
               "icons/linkTargetNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup source = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcInterfaceExtends_4004_source,
               "icons/linkSourceNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         if (!target.isEmpty()) {
            result.add(target);
         }
         if (!source.isEmpty()) {
            result.add(source);
         }
         return result.toArray();
      }

      case DbcModelEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Diagram sv = (Diagram) view;
         DbCNavigatorGroup links = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcModel_1000_links,
               "icons/linksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcPackageEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnumEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getDiagramLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         links.addChildren(createNavigatorItems(connectedViews, links, false));
         connectedViews = getDiagramLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         links.addChildren(createNavigatorItems(connectedViews, links, false));
         connectedViews = getDiagramLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassExtendsEditPart.VISUAL_ID));
         links.addChildren(createNavigatorItems(connectedViews, links, false));
         connectedViews = getDiagramLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcInterfaceExtendsEditPart.VISUAL_ID));
         links.addChildren(createNavigatorItems(connectedViews, links, false));
         connectedViews = getDiagramLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
         links.addChildren(createNavigatorItems(connectedViews, links, false));
         if (!links.isEmpty()) {
            result.add(links);
         }
         return result.toArray();
      }

      case DbcProofReferenceEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Edge sv = (Edge) view;
         DbCNavigatorGroup target = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcProofReference_4002_target,
               "icons/linkTargetNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup source = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcProofReference_4002_source,
               "icons/linkSourceNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnumEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcOperationContractEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcConstructorEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnumLiteralEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbCAxiomContractEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofEditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         if (!target.isEmpty()) {
            result.add(target);
         }
         if (!source.isEmpty()) {
            result.add(source);
         }
         return result.toArray();
      }

      case AbstractDbcClassImplementsEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Edge sv = (Edge) view;
         DbCNavigatorGroup target = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_AbstractDbcClassImplements_4005_target,
               "icons/linkTargetNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         DbCNavigatorGroup source = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_AbstractDbcClassImplements_4005_source,
               "icons/linkSourceNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksTargetByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         target.addChildren(createNavigatorItems(connectedViews, target, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnumEditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         connectedViews = getLinksSourceByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         source.addChildren(createNavigatorItems(connectedViews, source, true));
         if (!target.isEmpty()) {
            result.add(target);
         }
         if (!source.isEmpty()) {
            result.add(source);
         }
         return result.toArray();
      }

      case DbcPackageEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcPackage2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(
               Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         return result.toArray();
      }

      case DbcMethodEditPart.VISUAL_ID: {
         LinkedList<DbCAbstractNavigatorItem> result = new LinkedList<DbCAbstractNavigatorItem>();
         Node sv = (Node) view;
         DbCNavigatorGroup incominglinks = new DbCNavigatorGroup(
               Messages.NavigatorGroupName_DbcMethod_3009_incominglinks,
               "icons/incomingLinksNavigatorGroup.gif", parentElement); //$NON-NLS-1$
         Collection<View> connectedViews;
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getChildrenByType(Collections.singleton(sv),
               DbCVisualIDRegistry
                     .getType(DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID));
         connectedViews = getChildrenByType(connectedViews,
               DbCVisualIDRegistry
                     .getType(DbcOperationContractEditPart.VISUAL_ID));
         result.addAll(createNavigatorItems(connectedViews, parentElement,
               false));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofTargetEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         connectedViews = getIncomingLinksByType(Collections.singleton(sv),
               DbCVisualIDRegistry.getType(DbcProofReferenceEditPart.VISUAL_ID));
         incominglinks.addChildren(createNavigatorItems(connectedViews,
               incominglinks, true));
         if (!incominglinks.isEmpty()) {
            result.add(incominglinks);
         }
         return result.toArray();
      }
      }
      return EMPTY_ARRAY;
   }

   /**
    * @generated
    */
   private Collection<View> getLinksSourceByType(Collection<Edge> edges,
         String type) {
      LinkedList<View> result = new LinkedList<View>();
      for (Edge nextEdge : edges) {
         View nextEdgeSource = nextEdge.getSource();
         if (type.equals(nextEdgeSource.getType()) && isOwnView(nextEdgeSource)) {
            result.add(nextEdgeSource);
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private Collection<View> getLinksTargetByType(Collection<Edge> edges,
         String type) {
      LinkedList<View> result = new LinkedList<View>();
      for (Edge nextEdge : edges) {
         View nextEdgeTarget = nextEdge.getTarget();
         if (type.equals(nextEdgeTarget.getType()) && isOwnView(nextEdgeTarget)) {
            result.add(nextEdgeTarget);
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private Collection<View> getOutgoingLinksByType(
         Collection<? extends View> nodes, String type) {
      LinkedList<View> result = new LinkedList<View>();
      for (View nextNode : nodes) {
         result.addAll(selectViewsByType(nextNode.getSourceEdges(), type));
      }
      return result;
   }

   /**
    * @generated
    */
   private Collection<View> getIncomingLinksByType(
         Collection<? extends View> nodes, String type) {
      LinkedList<View> result = new LinkedList<View>();
      for (View nextNode : nodes) {
         result.addAll(selectViewsByType(nextNode.getTargetEdges(), type));
      }
      return result;
   }

   /**
    * @generated
    */
   private Collection<View> getChildrenByType(Collection<? extends View> nodes,
         String type) {
      LinkedList<View> result = new LinkedList<View>();
      for (View nextNode : nodes) {
         result.addAll(selectViewsByType(nextNode.getChildren(), type));
      }
      return result;
   }

   /**
    * @generated
    */
   private Collection<View> getDiagramLinksByType(Collection<Diagram> diagrams,
         String type) {
      ArrayList<View> result = new ArrayList<View>();
      for (Diagram nextDiagram : diagrams) {
         result.addAll(selectViewsByType(nextDiagram.getEdges(), type));
      }
      return result;
   }

   // TODO refactor as static method
   /**
    * @generated
    */
   private Collection<View> selectViewsByType(Collection<View> views,
         String type) {
      ArrayList<View> result = new ArrayList<View>();
      for (View nextView : views) {
         if (type.equals(nextView.getType()) && isOwnView(nextView)) {
            result.add(nextView);
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private boolean isOwnView(View view) {
      return DbcModelEditPart.MODEL_ID.equals(DbCVisualIDRegistry
            .getModelID(view));
   }

   /**
    * @generated
    */
   private Collection<DbCNavigatorItem> createNavigatorItems(
         Collection<View> views, Object parent, boolean isLeafs) {
      ArrayList<DbCNavigatorItem> result = new ArrayList<DbCNavigatorItem>(
            views.size());
      for (View nextView : views) {
         result.add(new DbCNavigatorItem(nextView, parent, isLeafs));
      }
      return result;
   }

   /**
    * @generated
    */
   public Object getParent(Object element) {
      if (element instanceof DbCAbstractNavigatorItem) {
         DbCAbstractNavigatorItem abstractNavigatorItem = (DbCAbstractNavigatorItem) element;
         return abstractNavigatorItem.getParent();
      }
      return null;
   }

   /**
    * @generated
    */
   public boolean hasChildren(Object element) {
      return element instanceof IFile || getChildren(element).length > 0;
   }

}