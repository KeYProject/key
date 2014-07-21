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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.policies;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.diagram.core.util.ViewUtil;
import org.eclipse.gmf.runtime.diagram.ui.commands.DeferredLayoutCommand;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.commands.SetViewMutabilityCommand;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.CanonicalEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateConnectionViewRequest;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateViewRequest;
import org.eclipse.gmf.runtime.diagram.ui.requests.RequestConstants;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.Node;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackage2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramUpdater;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCLinkDescriptor;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCNodeDescriptor;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbcModelCanonicalEditPolicy extends CanonicalEditPolicy {

   /**
    * @generated
    */
   private Set<EStructuralFeature> myFeaturesToSynchronize;

   /**
    * @generated
    */
   protected void refreshOnActivate() {
      // Need to activate editpart children before invoking the canonical refresh for EditParts to add event listeners
      List<?> c = getHost().getChildren();
      for (int i = 0; i < c.size(); i++) {
         ((EditPart) c.get(i)).activate();
      }
      super.refreshOnActivate();
   }

   /**
    * @generated
    */
   protected Set getFeaturesToSynchronize() {
      if (myFeaturesToSynchronize == null) {
         myFeaturesToSynchronize = new HashSet<EStructuralFeature>();
         myFeaturesToSynchronize.add(DbcmodelPackage.eINSTANCE
               .getAbstractDbCContainer_Packages());
         myFeaturesToSynchronize.add(DbcmodelPackage.eINSTANCE
               .getAbstractDbcTypeContainer_Types());
         myFeaturesToSynchronize.add(DbcmodelPackage.eINSTANCE
               .getAbstractDbcProofContainer_Proofs());
      }
      return myFeaturesToSynchronize;
   }

   /**
    * @generated
    */
   @SuppressWarnings("rawtypes")
   protected List getSemanticChildrenList() {
      View viewObject = (View) getHost().getModel();
      LinkedList<EObject> result = new LinkedList<EObject>();
      List<DbCNodeDescriptor> childDescriptors = DbCDiagramUpdater
            .getDbcModel_1000SemanticChildren(viewObject);
      for (DbCNodeDescriptor d : childDescriptors) {
         result.add(d.getModelElement());
      }
      return result;
   }

   /**
    * @generated
    */
   protected boolean isOrphaned(Collection<EObject> semanticChildren,
         final View view) {
      return isMyDiagramElement(view)
            && !semanticChildren.contains(view.getElement());
   }

   /**
    * @generated
    */
   private boolean isMyDiagramElement(View view) {
      int visualID = DbCVisualIDRegistry.getVisualID(view);
      switch (visualID) {
      case DbcPackageEditPart.VISUAL_ID:
      case DbcInterfaceEditPart.VISUAL_ID:
      case DbcClassEditPart.VISUAL_ID:
      case DbcEnumEditPart.VISUAL_ID:
      case DbcProofEditPart.VISUAL_ID:
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected void refreshSemantic() {
      if (resolveSemanticElement() == null) {
         return;
      }
      LinkedList<IAdaptable> createdViews = new LinkedList<IAdaptable>();
      List<DbCNodeDescriptor> childDescriptors = DbCDiagramUpdater
            .getDbcModel_1000SemanticChildren((View) getHost().getModel());
      LinkedList<View> orphaned = new LinkedList<View>();
      // we care to check only views we recognize as ours
      LinkedList<View> knownViewChildren = new LinkedList<View>();
      for (View v : getViewChildren()) {
         if (isMyDiagramElement(v)) {
            knownViewChildren.add(v);
         }
      }
      // alternative to #cleanCanonicalSemanticChildren(getViewChildren(), semanticChildren)
      //
      // iteration happens over list of desired semantic elements, trying to find best matching View, while original CEP
      // iterates views, potentially losing view (size/bounds) information - i.e. if there are few views to reference same EObject, only last one 
      // to answer isOrphaned == true will be used for the domain element representation, see #cleanCanonicalSemanticChildren()
      for (Iterator<DbCNodeDescriptor> descriptorsIterator = childDescriptors
            .iterator(); descriptorsIterator.hasNext();) {
         DbCNodeDescriptor next = descriptorsIterator.next();
         String hint = DbCVisualIDRegistry.getType(next.getVisualID());
         LinkedList<View> perfectMatch = new LinkedList<View>(); // both semanticElement and hint match that of NodeDescriptor
         for (View childView : getViewChildren()) {
            EObject semanticElement = childView.getElement();
            if (next.getModelElement().equals(semanticElement)) {
               if (hint.equals(childView.getType())) {
                  perfectMatch.add(childView);
                  // actually, can stop iteration over view children here, but
                  // may want to use not the first view but last one as a 'real' match (the way original CEP does
                  // with its trick with viewToSemanticMap inside #cleanCanonicalSemanticChildren
               }
            }
         }
         if (perfectMatch.size() > 0) {
            descriptorsIterator.remove(); // precise match found no need to create anything for the NodeDescriptor
            // use only one view (first or last?), keep rest as orphaned for further consideration
            knownViewChildren.remove(perfectMatch.getFirst());
         }
      }
      // those left in knownViewChildren are subject to removal - they are our diagram elements we didn't find match to,
      // or those we have potential matches to, and thus need to be recreated, preserving size/location information.
      orphaned.addAll(knownViewChildren);
      //
      ArrayList<CreateViewRequest.ViewDescriptor> viewDescriptors = new ArrayList<CreateViewRequest.ViewDescriptor>(
            childDescriptors.size());
      for (DbCNodeDescriptor next : childDescriptors) {
         String hint = DbCVisualIDRegistry.getType(next.getVisualID());
         IAdaptable elementAdapter = new CanonicalElementAdapter(
               next.getModelElement(), hint);
         CreateViewRequest.ViewDescriptor descriptor = new CreateViewRequest.ViewDescriptor(
               elementAdapter, Node.class, hint, ViewUtil.APPEND, false, host()
                     .getDiagramPreferencesHint());
         viewDescriptors.add(descriptor);
      }

      boolean changed = deleteViews(orphaned.iterator());
      //
      CreateViewRequest request = getCreateViewRequest(viewDescriptors);
      Command cmd = getCreateViewCommand(request);
      if (cmd != null && cmd.canExecute()) {
         SetViewMutabilityCommand.makeMutable(
               new EObjectAdapter(host().getNotationView())).execute();
         executeCommand(cmd);
         @SuppressWarnings("unchecked")
         List<IAdaptable> nl = (List<IAdaptable>) request.getNewObject();
         createdViews.addAll(nl);
      }
      if (changed || createdViews.size() > 0) {
         postProcessRefreshSemantic(createdViews);
      }

      Collection<IAdaptable> createdConnectionViews = refreshConnections();

      if (createdViews.size() > 1) {
         // perform a layout of the container
         DeferredLayoutCommand layoutCmd = new DeferredLayoutCommand(host()
               .getEditingDomain(), createdViews, host());
         executeCommand(new ICommandProxy(layoutCmd));
      }

      createdViews.addAll(createdConnectionViews);

      makeViewsImmutable(createdViews);
   }

   /**
    * @generated
    */
   private Collection<IAdaptable> refreshConnections() {
      Map<EObject, View> domain2NotationMap = new HashMap<EObject, View>();
      Collection<DbCLinkDescriptor> linkDescriptors = collectAllLinks(
            getDiagram(), domain2NotationMap);
      Collection existingLinks = new LinkedList(getDiagram().getEdges());
      for (Iterator linksIterator = existingLinks.iterator(); linksIterator
            .hasNext();) {
         Edge nextDiagramLink = (Edge) linksIterator.next();
         int diagramLinkVisualID = DbCVisualIDRegistry
               .getVisualID(nextDiagramLink);
         if (diagramLinkVisualID == -1) {
            if (nextDiagramLink.getSource() != null
                  && nextDiagramLink.getTarget() != null) {
               linksIterator.remove();
            }
            continue;
         }
         EObject diagramLinkObject = nextDiagramLink.getElement();
         EObject diagramLinkSrc = nextDiagramLink.getSource().getElement();
         EObject diagramLinkDst = nextDiagramLink.getTarget().getElement();
         for (Iterator<DbCLinkDescriptor> linkDescriptorsIterator = linkDescriptors
               .iterator(); linkDescriptorsIterator.hasNext();) {
            DbCLinkDescriptor nextLinkDescriptor = linkDescriptorsIterator
                  .next();
            if (diagramLinkObject == nextLinkDescriptor.getModelElement()
                  && diagramLinkSrc == nextLinkDescriptor.getSource()
                  && diagramLinkDst == nextLinkDescriptor.getDestination()
                  && diagramLinkVisualID == nextLinkDescriptor.getVisualID()) {
               linksIterator.remove();
               linkDescriptorsIterator.remove();
               break;
            }
         }
      }
      deleteViews(existingLinks.iterator());
      return createConnections(linkDescriptors, domain2NotationMap);
   }

   /**
    * @generated
    */
   private Collection<DbCLinkDescriptor> collectAllLinks(View view,
         Map<EObject, View> domain2NotationMap) {
      if (!DbcModelEditPart.MODEL_ID.equals(DbCVisualIDRegistry
            .getModelID(view))) {
         return Collections.emptyList();
      }
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcModelEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcModel_1000ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcPackageEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcPackage_2007ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcInterfaceEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcInterface_2011ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcClassEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcClass_2012ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcEnumEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater.getDbcEnum_2013ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcProofEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcProof_2014ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcPackage2EditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcPackage_3027ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcClass2EditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcClass_3031ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcInterface2EditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcInterface_3032ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcEnum2EditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater.getDbcEnum_3033ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcProof2EditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcProof_3034ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcInvariantEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcInvariant_3035ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcAttributeEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcAttribute_3011ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcMethodEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcMethod_3009ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcOperationContractEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcOperationContract_3026ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcConstructorEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcConstructor_3010ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcEnumLiteralEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcEnumLiteral_3020ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcAxiomEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcAxiom_3036ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbCAxiomContractEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbCAxiomContract_3037ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      case DbcProofReferenceEditPart.VISUAL_ID: {
         if (!domain2NotationMap.containsKey(view.getElement())) {
            result.addAll(DbCDiagramUpdater
                  .getDbcProofReference_4002ContainedLinks(view));
         }
         if (!domain2NotationMap.containsKey(view.getElement())
               || view.getEAnnotation("Shortcut") == null) { //$NON-NLS-1$
            domain2NotationMap.put(view.getElement(), view);
         }
         break;
      }
      }
      for (Iterator children = view.getChildren().iterator(); children
            .hasNext();) {
         result.addAll(collectAllLinks((View) children.next(),
               domain2NotationMap));
      }
      for (Iterator edges = view.getSourceEdges().iterator(); edges.hasNext();) {
         result.addAll(collectAllLinks((View) edges.next(), domain2NotationMap));
      }
      return result;
   }

   /**
    * @generated
    */
   private Collection<IAdaptable> createConnections(
         Collection<DbCLinkDescriptor> linkDescriptors,
         Map<EObject, View> domain2NotationMap) {
      LinkedList<IAdaptable> adapters = new LinkedList<IAdaptable>();
      for (DbCLinkDescriptor nextLinkDescriptor : linkDescriptors) {
         EditPart sourceEditPart = getEditPart(nextLinkDescriptor.getSource(),
               domain2NotationMap);
         EditPart targetEditPart = getEditPart(
               nextLinkDescriptor.getDestination(), domain2NotationMap);
         if (sourceEditPart == null || targetEditPart == null) {
            continue;
         }
         CreateConnectionViewRequest.ConnectionViewDescriptor descriptor = new CreateConnectionViewRequest.ConnectionViewDescriptor(
               nextLinkDescriptor.getSemanticAdapter(),
               DbCVisualIDRegistry.getType(nextLinkDescriptor.getVisualID()),
               ViewUtil.APPEND, false,
               ((IGraphicalEditPart) getHost()).getDiagramPreferencesHint());
         CreateConnectionViewRequest ccr = new CreateConnectionViewRequest(
               descriptor);
         ccr.setType(RequestConstants.REQ_CONNECTION_START);
         ccr.setSourceEditPart(sourceEditPart);
         sourceEditPart.getCommand(ccr);
         ccr.setTargetEditPart(targetEditPart);
         ccr.setType(RequestConstants.REQ_CONNECTION_END);
         Command cmd = targetEditPart.getCommand(ccr);
         if (cmd != null && cmd.canExecute()) {
            executeCommand(cmd);
            IAdaptable viewAdapter = (IAdaptable) ccr.getNewObject();
            if (viewAdapter != null) {
               adapters.add(viewAdapter);
            }
         }
      }
      return adapters;
   }

   /**
    * @generated
    */
   private EditPart getEditPart(EObject domainModelElement,
         Map<EObject, View> domain2NotationMap) {
      View view = (View) domain2NotationMap.get(domainModelElement);
      if (view != null) {
         return (EditPart) getHost().getViewer().getEditPartRegistry()
               .get(view);
      }
      return null;
   }

   /**
    * @generated
    */
   private Diagram getDiagram() {
      return ((View) getHost().getModel()).getDiagram();
   }
}