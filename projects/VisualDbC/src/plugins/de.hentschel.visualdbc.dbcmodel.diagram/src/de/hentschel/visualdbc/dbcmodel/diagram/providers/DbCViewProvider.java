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

package de.hentschel.visualdbc.dbcmodel.diagram.providers;

import java.util.ArrayList;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EcoreFactory;
import org.eclipse.emf.transaction.util.TransactionUtil;
import org.eclipse.gmf.runtime.common.core.service.AbstractProvider;
import org.eclipse.gmf.runtime.common.core.service.IOperation;
import org.eclipse.gmf.runtime.diagram.core.preferences.PreferencesHint;
import org.eclipse.gmf.runtime.diagram.core.providers.IViewProvider;
import org.eclipse.gmf.runtime.diagram.core.services.view.CreateDiagramViewOperation;
import org.eclipse.gmf.runtime.diagram.core.services.view.CreateEdgeViewOperation;
import org.eclipse.gmf.runtime.diagram.core.services.view.CreateNodeViewOperation;
import org.eclipse.gmf.runtime.diagram.core.services.view.CreateViewForKindOperation;
import org.eclipse.gmf.runtime.diagram.core.services.view.CreateViewOperation;
import org.eclipse.gmf.runtime.diagram.core.util.ViewUtil;
import org.eclipse.gmf.runtime.diagram.ui.preferences.IPreferenceConstants;
import org.eclipse.gmf.runtime.draw2d.ui.figures.FigureUtilities;
import org.eclipse.gmf.runtime.emf.core.util.EMFCoreUtil;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.type.core.IHintedType;
import org.eclipse.gmf.runtime.notation.Connector;
import org.eclipse.gmf.runtime.notation.DecorationNode;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.Edge;
import org.eclipse.gmf.runtime.notation.FontStyle;
import org.eclipse.gmf.runtime.notation.Location;
import org.eclipse.gmf.runtime.notation.MeasurementUnit;
import org.eclipse.gmf.runtime.notation.Node;
import org.eclipse.gmf.runtime.notation.NotationFactory;
import org.eclipse.gmf.runtime.notation.NotationPackage;
import org.eclipse.gmf.runtime.notation.RelativeBendpoints;
import org.eclipse.gmf.runtime.notation.Routing;
import org.eclipse.gmf.runtime.notation.Shape;
import org.eclipse.gmf.runtime.notation.TitleStyle;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.gmf.runtime.notation.datatype.RelativeBendpoint;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.FontData;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.AbstractDbcClassImplementsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractDepEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractPreEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeNameTypeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomDbcAxiomCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomDefinitionEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassAttributeCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassAttributeCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorDbcConstructorCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorSignatureEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumAttributeCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumAttributeCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumLiteralCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumLiteralCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceAttributeCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceAttributeCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantTextEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodDbcMethodCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodSignatureReturnTypeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractPostEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractPreEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackage2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofObligation2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofObligationEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceKindEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofTargetEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbCViewProvider extends AbstractProvider implements IViewProvider {

   /**
    * @generated
    */
   public final boolean provides(IOperation operation) {
      if (operation instanceof CreateViewForKindOperation) {
         return provides((CreateViewForKindOperation) operation);
      }
      assert operation instanceof CreateViewOperation;
      if (operation instanceof CreateDiagramViewOperation) {
         return provides((CreateDiagramViewOperation) operation);
      }
      else if (operation instanceof CreateEdgeViewOperation) {
         return provides((CreateEdgeViewOperation) operation);
      }
      else if (operation instanceof CreateNodeViewOperation) {
         return provides((CreateNodeViewOperation) operation);
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean provides(CreateViewForKindOperation op) {
      /*
       if (op.getViewKind() == Node.class)
       return getNodeViewClass(op.getSemanticAdapter(), op.getContainerView(), op.getSemanticHint()) != null;
       if (op.getViewKind() == Edge.class)
       return getEdgeViewClass(op.getSemanticAdapter(), op.getContainerView(), op.getSemanticHint()) != null;
       */
      return true;
   }

   /**
    * @generated
    */
   protected boolean provides(CreateDiagramViewOperation op) {
      return DbcModelEditPart.MODEL_ID.equals(op.getSemanticHint())
            && DbCVisualIDRegistry.getDiagramVisualID(getSemanticElement(op
                  .getSemanticAdapter())) != -1;
   }

   /**
    * @generated
    */
   protected boolean provides(CreateNodeViewOperation op) {
      if (op.getContainerView() == null) {
         return false;
      }
      IElementType elementType = getSemanticElementType(op.getSemanticAdapter());
      EObject domainElement = getSemanticElement(op.getSemanticAdapter());
      int visualID;
      if (op.getSemanticHint() == null) {
         // Semantic hint is not specified. Can be a result of call from CanonicalEditPolicy.
         // In this situation there should be NO elementType, visualID will be determined
         // by VisualIDRegistry.getNodeVisualID() for domainElement.
         if (elementType != null || domainElement == null) {
            return false;
         }
         visualID = DbCVisualIDRegistry.getNodeVisualID(op.getContainerView(),
               domainElement);
      }
      else {
         visualID = DbCVisualIDRegistry.getVisualID(op.getSemanticHint());
         if (elementType != null) {
            if (!DbCElementTypes.isKnownElementType(elementType)
                  || (!(elementType instanceof IHintedType))) {
               return false; // foreign element type
            }
            String elementTypeHint = ((IHintedType) elementType)
                  .getSemanticHint();
            if (!op.getSemanticHint().equals(elementTypeHint)) {
               return false; // if semantic hint is specified it should be the same as in element type
            }
            if (domainElement != null
                  && visualID != DbCVisualIDRegistry.getNodeVisualID(
                        op.getContainerView(), domainElement)) {
               return false; // visual id for node EClass should match visual id from element type
            }
         }
         else {
            if (!DbcModelEditPart.MODEL_ID.equals(DbCVisualIDRegistry
                  .getModelID(op.getContainerView()))) {
               return false; // foreign diagram
            }
            switch (visualID) {
            case DbcPackageEditPart.VISUAL_ID:
            case DbcClass2EditPart.VISUAL_ID:
            case DbcInterface2EditPart.VISUAL_ID:
            case DbcEnum2EditPart.VISUAL_ID:
            case DbcProof2EditPart.VISUAL_ID:
            case DbcInvariantEditPart.VISUAL_ID:
            case DbcAttributeEditPart.VISUAL_ID:
            case DbcMethodEditPart.VISUAL_ID:
            case DbcOperationContractEditPart.VISUAL_ID:
            case DbcConstructorEditPart.VISUAL_ID:
            case DbcEnumLiteralEditPart.VISUAL_ID:
            case DbcAxiomEditPart.VISUAL_ID:
            case DbCAxiomContractEditPart.VISUAL_ID:
            case DbcInterfaceEditPart.VISUAL_ID:
            case DbcClassEditPart.VISUAL_ID:
            case DbcEnumEditPart.VISUAL_ID:
            case DbcProofEditPart.VISUAL_ID:
            case DbcPackage2EditPart.VISUAL_ID:
               if (domainElement == null
                     || visualID != DbCVisualIDRegistry.getNodeVisualID(
                           op.getContainerView(), domainElement)) {
                  return false; // visual id in semantic hint should match visual id for domain element
               }
               break;
            default:
               return false;
            }
         }
      }
      return DbcPackageEditPart.VISUAL_ID == visualID
            || DbcInterfaceEditPart.VISUAL_ID == visualID
            || DbcClassEditPart.VISUAL_ID == visualID
            || DbcEnumEditPart.VISUAL_ID == visualID
            || DbcProofEditPart.VISUAL_ID == visualID
            || DbcPackage2EditPart.VISUAL_ID == visualID
            || DbcClass2EditPart.VISUAL_ID == visualID
            || DbcInterface2EditPart.VISUAL_ID == visualID
            || DbcEnum2EditPart.VISUAL_ID == visualID
            || DbcProof2EditPart.VISUAL_ID == visualID
            || DbcInvariantEditPart.VISUAL_ID == visualID
            || DbcAttributeEditPart.VISUAL_ID == visualID
            || DbcMethodEditPart.VISUAL_ID == visualID
            || DbcOperationContractEditPart.VISUAL_ID == visualID
            || DbcConstructorEditPart.VISUAL_ID == visualID
            || DbcEnumLiteralEditPart.VISUAL_ID == visualID
            || DbcAxiomEditPart.VISUAL_ID == visualID
            || DbCAxiomContractEditPart.VISUAL_ID == visualID;
   }

   /**
    * @generated
    */
   protected boolean provides(CreateEdgeViewOperation op) {
      IElementType elementType = getSemanticElementType(op.getSemanticAdapter());
      if (!DbCElementTypes.isKnownElementType(elementType)
            || (!(elementType instanceof IHintedType))) {
         return false; // foreign element type
      }
      String elementTypeHint = ((IHintedType) elementType).getSemanticHint();
      if (elementTypeHint == null
            || (op.getSemanticHint() != null && !elementTypeHint.equals(op
                  .getSemanticHint()))) {
         return false; // our hint is visual id and must be specified, and it should be the same as in element type
      }
      int visualID = DbCVisualIDRegistry.getVisualID(elementTypeHint);
      EObject domainElement = getSemanticElement(op.getSemanticAdapter());
      if (domainElement != null
            && visualID != DbCVisualIDRegistry
                  .getLinkWithClassVisualID(domainElement)) {
         return false; // visual id for link EClass should match visual id from element type
      }
      return true;
   }

   /**
    * @generated
    */
   public Diagram createDiagram(IAdaptable semanticAdapter, String diagramKind,
         PreferencesHint preferencesHint) {
      Diagram diagram = NotationFactory.eINSTANCE.createDiagram();
      diagram.getStyles().add(NotationFactory.eINSTANCE.createDiagramStyle());
      diagram.setType(DbcModelEditPart.MODEL_ID);
      diagram.setElement(getSemanticElement(semanticAdapter));
      diagram.setMeasurementUnit(MeasurementUnit.PIXEL_LITERAL);
      return diagram;
   }

   /**
    * @generated
    */
   public Node createNode(IAdaptable semanticAdapter, View containerView,
         String semanticHint, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      final EObject domainElement = getSemanticElement(semanticAdapter);
      final int visualID;
      if (semanticHint == null) {
         visualID = DbCVisualIDRegistry.getNodeVisualID(containerView,
               domainElement);
      }
      else {
         visualID = DbCVisualIDRegistry.getVisualID(semanticHint);
      }
      switch (visualID) {
      case DbcPackageEditPart.VISUAL_ID:
         return createDbcPackage_2007(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcInterfaceEditPart.VISUAL_ID:
         return createDbcInterface_2011(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcClassEditPart.VISUAL_ID:
         return createDbcClass_2012(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcEnumEditPart.VISUAL_ID:
         return createDbcEnum_2013(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcProofEditPart.VISUAL_ID:
         return createDbcProof_2014(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcPackage2EditPart.VISUAL_ID:
         return createDbcPackage_3027(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcClass2EditPart.VISUAL_ID:
         return createDbcClass_3031(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcInterface2EditPart.VISUAL_ID:
         return createDbcInterface_3032(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcEnum2EditPart.VISUAL_ID:
         return createDbcEnum_3033(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcProof2EditPart.VISUAL_ID:
         return createDbcProof_3034(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcInvariantEditPart.VISUAL_ID:
         return createDbcInvariant_3035(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcAttributeEditPart.VISUAL_ID:
         return createDbcAttribute_3011(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcMethodEditPart.VISUAL_ID:
         return createDbcMethod_3009(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcOperationContractEditPart.VISUAL_ID:
         return createDbcOperationContract_3026(domainElement, containerView,
               index, persisted, preferencesHint);
      case DbcConstructorEditPart.VISUAL_ID:
         return createDbcConstructor_3010(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return createDbcEnumLiteral_3020(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbcAxiomEditPart.VISUAL_ID:
         return createDbcAxiom_3036(domainElement, containerView, index,
               persisted, preferencesHint);
      case DbCAxiomContractEditPart.VISUAL_ID:
         return createDbCAxiomContract_3037(domainElement, containerView,
               index, persisted, preferencesHint);
      }
      // can't happen, provided #provides(CreateNodeViewOperation) is correct
      return null;
   }

   /**
    * @generated
    */
   public Edge createEdge(IAdaptable semanticAdapter, View containerView,
         String semanticHint, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      IElementType elementType = getSemanticElementType(semanticAdapter);
      String elementTypeHint = ((IHintedType) elementType).getSemanticHint();
      switch (DbCVisualIDRegistry.getVisualID(elementTypeHint)) {
      case DbcProofTargetEditPart.VISUAL_ID:
         return createDbcProofTarget_4001(containerView, index, persisted,
               preferencesHint);
      case DbcProofReferenceEditPart.VISUAL_ID:
         return createDbcProofReference_4002(
               getSemanticElement(semanticAdapter), containerView, index,
               persisted, preferencesHint);
      case DbcClassExtendsEditPart.VISUAL_ID:
         return createDbcClassExtends_4003(containerView, index, persisted,
               preferencesHint);
      case DbcInterfaceExtendsEditPart.VISUAL_ID:
         return createDbcInterfaceExtends_4004(containerView, index, persisted,
               preferencesHint);
      case AbstractDbcClassImplementsEditPart.VISUAL_ID:
         return createAbstractDbcClassImplements_4005(containerView, index,
               persisted, preferencesHint);
      }
      // can never happen, provided #provides(CreateEdgeViewOperation) is correct
      return null;
   }

   /**
    * @generated
    */
   public Node createDbcPackage_2007(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Shape node = NotationFactory.eINSTANCE.createShape();
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcPackageEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      stampShortcut(containerView, node);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      org.eclipse.swt.graphics.RGB fillRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_FILL_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getFillStyle_FillColor(),
            FigureUtilities.RGBToInteger(fillRGB));
      Node label5042 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcPackageNameEditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcInterface_2011(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcInterfaceEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      stampShortcut(containerView, node);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5049 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcInterfaceNameEditPart.VISUAL_ID));
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID),
            true, false, false, false);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID),
            true, false, true, true);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcClass_2012(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcClassEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      stampShortcut(containerView, node);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5050 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcClassNameEditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID),
            true, false, false, false);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID),
            true, false, true, true);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcEnum_2013(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcEnumEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      stampShortcut(containerView, node);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5051 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcEnumNameEditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID),
            true, false, false, false);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID),
            true, false, true, true);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID),
            true, false, true, true);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcProof_2014(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcProofEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      stampShortcut(containerView, node);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5053 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcProofObligationEditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcPackage_3027(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Shape node = NotationFactory.eINSTANCE.createShape();
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcPackage2EditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      org.eclipse.swt.graphics.RGB fillRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_FILL_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getFillStyle_FillColor(),
            FigureUtilities.RGBToInteger(fillRGB));
      Node label5041 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcPackageName2EditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID),
            true, false, false, false);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcClass_3031(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcClass2EditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5048 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcClassName2EditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID),
            true, false, true, true);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcInterface_3032(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcInterface2EditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5047 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcInterfaceName2EditPart.VISUAL_ID));
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID),
            true, false, true, true);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcEnum_3033(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcEnum2EditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5046 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcEnumName2EditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID),
            true, false, true, true);
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID),
            true, false, true, true);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcProof_3034(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcProof2EditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5052 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcProofObligation2EditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcInvariant_3035(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Shape node = NotationFactory.eINSTANCE.createShape();
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcInvariantEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      org.eclipse.swt.graphics.RGB fillRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_FILL_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getFillStyle_FillColor(),
            FigureUtilities.RGBToInteger(fillRGB));
      Node label5054 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcInvariantNameEditPart.VISUAL_ID));
      Node label5055 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcInvariantTextEditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcAttribute_3011(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcAttributeEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5061 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcAttributeNameTypeEditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcMethod_3009(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Shape node = NotationFactory.eINSTANCE.createShape();
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcMethodEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      org.eclipse.swt.graphics.RGB fillRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_FILL_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getFillStyle_FillColor(),
            FigureUtilities.RGBToInteger(fillRGB));
      Node label5011 = createLabel(node,
            DbCVisualIDRegistry
                  .getType(DbcMethodSignatureReturnTypeEditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcOperationContract_3026(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry
            .getType(DbcOperationContractEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5035 = createLabel(node,
            DbCVisualIDRegistry
                  .getType(DbcOperationContractNameEditPart.VISUAL_ID));
      Node label5036 = createLabel(node,
            DbCVisualIDRegistry
                  .getType(DbcOperationContractPreEditPart.VISUAL_ID));
      Node label5037 = createLabel(node,
            DbCVisualIDRegistry
                  .getType(DbcOperationContractPostEditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcConstructor_3010(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Shape node = NotationFactory.eINSTANCE.createShape();
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry
            .getType(DbcConstructorEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      org.eclipse.swt.graphics.RGB fillRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_FILL_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getFillStyle_FillColor(),
            FigureUtilities.RGBToInteger(fillRGB));
      Node label5012 = createLabel(node,
            DbCVisualIDRegistry
                  .getType(DbcConstructorSignatureEditPart.VISUAL_ID));
      createCompartment(
            node,
            DbCVisualIDRegistry
                  .getType(DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcEnumLiteral_3020(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry
            .getType(DbcEnumLiteralEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5062 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcEnumLiteralNameEditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Node createDbcAxiom_3036(EObject domainElement, View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Shape node = NotationFactory.eINSTANCE.createShape();
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry.getType(DbcAxiomEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      org.eclipse.swt.graphics.RGB fillRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_FILL_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getFillStyle_FillColor(),
            FigureUtilities.RGBToInteger(fillRGB));
      Node label5056 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcAxiomNameEditPart.VISUAL_ID));
      Node label5060 = createLabel(node,
            DbCVisualIDRegistry.getType(DbcAxiomDefinitionEditPart.VISUAL_ID));
      createCompartment(node,
            DbCVisualIDRegistry
                  .getType(DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID),
            true, false, false, false);
      return node;
   }

   /**
    * @generated
    */
   public Node createDbCAxiomContract_3037(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Node node = NotationFactory.eINSTANCE.createNode();
      node.getStyles().add(NotationFactory.eINSTANCE.createDescriptionStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      node.getStyles().add(NotationFactory.eINSTANCE.createLineStyle());
      node.setLayoutConstraint(NotationFactory.eINSTANCE.createBounds());
      node.setType(DbCVisualIDRegistry
            .getType(DbCAxiomContractEditPart.VISUAL_ID));
      ViewUtil.insertChildView(containerView, node, index, persisted);
      node.setElement(domainElement);
      // initializeFromPreferences 
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(node,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle nodeFontStyle = (FontStyle) node
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (nodeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         nodeFontStyle.setFontName(fontData.getName());
         nodeFontStyle.setFontHeight(fontData.getHeight());
         nodeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         nodeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         nodeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Node label5057 = createLabel(node,
            DbCVisualIDRegistry.getType(DbCAxiomContractNameEditPart.VISUAL_ID));
      Node label5058 = createLabel(node,
            DbCVisualIDRegistry.getType(DbCAxiomContractPreEditPart.VISUAL_ID));
      Node label5059 = createLabel(node,
            DbCVisualIDRegistry.getType(DbCAxiomContractDepEditPart.VISUAL_ID));
      return node;
   }

   /**
    * @generated
    */
   public Edge createDbcProofTarget_4001(View containerView, int index,
         boolean persisted, PreferencesHint preferencesHint) {
      Connector edge = NotationFactory.eINSTANCE.createConnector();
      edge.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      RelativeBendpoints bendpoints = NotationFactory.eINSTANCE
            .createRelativeBendpoints();
      ArrayList<RelativeBendpoint> points = new ArrayList<RelativeBendpoint>(2);
      points.add(new RelativeBendpoint());
      points.add(new RelativeBendpoint());
      bendpoints.setPoints(points);
      edge.setBendpoints(bendpoints);
      ViewUtil.insertChildView(containerView, edge, index, persisted);
      edge.setType(DbCVisualIDRegistry
            .getType(DbcProofTargetEditPart.VISUAL_ID));
      edge.setElement(null);
      // initializePreferences
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(edge,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle edgeFontStyle = (FontStyle) edge
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (edgeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         edgeFontStyle.setFontName(fontData.getName());
         edgeFontStyle.setFontHeight(fontData.getHeight());
         edgeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         edgeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         edgeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Routing routing = Routing.get(prefStore
            .getInt(IPreferenceConstants.PREF_LINE_STYLE));
      if (routing != null) {
         ViewUtil.setStructuralFeatureValue(edge,
               NotationPackage.eINSTANCE.getRoutingStyle_Routing(), routing);
      }
      return edge;
   }

   /**
    * @generated
    */
   public Edge createDbcProofReference_4002(EObject domainElement,
         View containerView, int index, boolean persisted,
         PreferencesHint preferencesHint) {
      Connector edge = NotationFactory.eINSTANCE.createConnector();
      edge.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      RelativeBendpoints bendpoints = NotationFactory.eINSTANCE
            .createRelativeBendpoints();
      ArrayList<RelativeBendpoint> points = new ArrayList<RelativeBendpoint>(2);
      points.add(new RelativeBendpoint());
      points.add(new RelativeBendpoint());
      bendpoints.setPoints(points);
      edge.setBendpoints(bendpoints);
      ViewUtil.insertChildView(containerView, edge, index, persisted);
      edge.setType(DbCVisualIDRegistry
            .getType(DbcProofReferenceEditPart.VISUAL_ID));
      edge.setElement(domainElement);
      // initializePreferences
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(edge,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle edgeFontStyle = (FontStyle) edge
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (edgeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         edgeFontStyle.setFontName(fontData.getName());
         edgeFontStyle.setFontHeight(fontData.getHeight());
         edgeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         edgeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         edgeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Routing routing = Routing.get(prefStore
            .getInt(IPreferenceConstants.PREF_LINE_STYLE));
      if (routing != null) {
         ViewUtil.setStructuralFeatureValue(edge,
               NotationPackage.eINSTANCE.getRoutingStyle_Routing(), routing);
      }
      Node label6001 = createLabel(edge,
            DbCVisualIDRegistry
                  .getType(DbcProofReferenceKindEditPart.VISUAL_ID));
      label6001.setLayoutConstraint(NotationFactory.eINSTANCE.createLocation());
      Location location6001 = (Location) label6001.getLayoutConstraint();
      location6001.setX(0);
      location6001.setY(40);
      return edge;
   }

   /**
    * @generated
    */
   public Edge createDbcClassExtends_4003(View containerView, int index,
         boolean persisted, PreferencesHint preferencesHint) {
      Connector edge = NotationFactory.eINSTANCE.createConnector();
      edge.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      RelativeBendpoints bendpoints = NotationFactory.eINSTANCE
            .createRelativeBendpoints();
      ArrayList<RelativeBendpoint> points = new ArrayList<RelativeBendpoint>(2);
      points.add(new RelativeBendpoint());
      points.add(new RelativeBendpoint());
      bendpoints.setPoints(points);
      edge.setBendpoints(bendpoints);
      ViewUtil.insertChildView(containerView, edge, index, persisted);
      edge.setType(DbCVisualIDRegistry
            .getType(DbcClassExtendsEditPart.VISUAL_ID));
      edge.setElement(null);
      // initializePreferences
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(edge,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle edgeFontStyle = (FontStyle) edge
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (edgeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         edgeFontStyle.setFontName(fontData.getName());
         edgeFontStyle.setFontHeight(fontData.getHeight());
         edgeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         edgeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         edgeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Routing routing = Routing.get(prefStore
            .getInt(IPreferenceConstants.PREF_LINE_STYLE));
      if (routing != null) {
         ViewUtil.setStructuralFeatureValue(edge,
               NotationPackage.eINSTANCE.getRoutingStyle_Routing(), routing);
      }
      return edge;
   }

   /**
    * @generated
    */
   public Edge createDbcInterfaceExtends_4004(View containerView, int index,
         boolean persisted, PreferencesHint preferencesHint) {
      Connector edge = NotationFactory.eINSTANCE.createConnector();
      edge.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      RelativeBendpoints bendpoints = NotationFactory.eINSTANCE
            .createRelativeBendpoints();
      ArrayList<RelativeBendpoint> points = new ArrayList<RelativeBendpoint>(2);
      points.add(new RelativeBendpoint());
      points.add(new RelativeBendpoint());
      bendpoints.setPoints(points);
      edge.setBendpoints(bendpoints);
      ViewUtil.insertChildView(containerView, edge, index, persisted);
      edge.setType(DbCVisualIDRegistry
            .getType(DbcInterfaceExtendsEditPart.VISUAL_ID));
      edge.setElement(null);
      // initializePreferences
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(edge,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle edgeFontStyle = (FontStyle) edge
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (edgeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         edgeFontStyle.setFontName(fontData.getName());
         edgeFontStyle.setFontHeight(fontData.getHeight());
         edgeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         edgeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         edgeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Routing routing = Routing.get(prefStore
            .getInt(IPreferenceConstants.PREF_LINE_STYLE));
      if (routing != null) {
         ViewUtil.setStructuralFeatureValue(edge,
               NotationPackage.eINSTANCE.getRoutingStyle_Routing(), routing);
      }
      return edge;
   }

   /**
    * @generated
    */
   public Edge createAbstractDbcClassImplements_4005(View containerView,
         int index, boolean persisted, PreferencesHint preferencesHint) {
      Connector edge = NotationFactory.eINSTANCE.createConnector();
      edge.getStyles().add(NotationFactory.eINSTANCE.createFontStyle());
      RelativeBendpoints bendpoints = NotationFactory.eINSTANCE
            .createRelativeBendpoints();
      ArrayList<RelativeBendpoint> points = new ArrayList<RelativeBendpoint>(2);
      points.add(new RelativeBendpoint());
      points.add(new RelativeBendpoint());
      bendpoints.setPoints(points);
      edge.setBendpoints(bendpoints);
      ViewUtil.insertChildView(containerView, edge, index, persisted);
      edge.setType(DbCVisualIDRegistry
            .getType(AbstractDbcClassImplementsEditPart.VISUAL_ID));
      edge.setElement(null);
      // initializePreferences
      final IPreferenceStore prefStore = (IPreferenceStore) preferencesHint
            .getPreferenceStore();

      org.eclipse.swt.graphics.RGB lineRGB = PreferenceConverter.getColor(
            prefStore, IPreferenceConstants.PREF_LINE_COLOR);
      ViewUtil.setStructuralFeatureValue(edge,
            NotationPackage.eINSTANCE.getLineStyle_LineColor(),
            FigureUtilities.RGBToInteger(lineRGB));
      FontStyle edgeFontStyle = (FontStyle) edge
            .getStyle(NotationPackage.Literals.FONT_STYLE);
      if (edgeFontStyle != null) {
         FontData fontData = PreferenceConverter.getFontData(prefStore,
               IPreferenceConstants.PREF_DEFAULT_FONT);
         edgeFontStyle.setFontName(fontData.getName());
         edgeFontStyle.setFontHeight(fontData.getHeight());
         edgeFontStyle.setBold((fontData.getStyle() & SWT.BOLD) != 0);
         edgeFontStyle.setItalic((fontData.getStyle() & SWT.ITALIC) != 0);
         org.eclipse.swt.graphics.RGB fontRGB = PreferenceConverter.getColor(
               prefStore, IPreferenceConstants.PREF_FONT_COLOR);
         edgeFontStyle.setFontColor(FigureUtilities.RGBToInteger(fontRGB)
               .intValue());
      }
      Routing routing = Routing.get(prefStore
            .getInt(IPreferenceConstants.PREF_LINE_STYLE));
      if (routing != null) {
         ViewUtil.setStructuralFeatureValue(edge,
               NotationPackage.eINSTANCE.getRoutingStyle_Routing(), routing);
      }
      return edge;
   }

   /**
    * @generated
    */
   private void stampShortcut(View containerView, Node target) {
      if (!DbcModelEditPart.MODEL_ID.equals(DbCVisualIDRegistry
            .getModelID(containerView))) {
         EAnnotation shortcutAnnotation = EcoreFactory.eINSTANCE
               .createEAnnotation();
         shortcutAnnotation.setSource("Shortcut"); //$NON-NLS-1$
         shortcutAnnotation.getDetails().put(
               "modelID", DbcModelEditPart.MODEL_ID); //$NON-NLS-1$
         target.getEAnnotations().add(shortcutAnnotation);
      }
   }

   /**
    * @generated
    */
   private Node createLabel(View owner, String hint) {
      DecorationNode rv = NotationFactory.eINSTANCE.createDecorationNode();
      rv.setType(hint);
      ViewUtil.insertChildView(owner, rv, ViewUtil.APPEND, true);
      return rv;
   }

   /**
    * @generated
    */
   private Node createCompartment(View owner, String hint, boolean canCollapse,
         boolean hasTitle, boolean canSort, boolean canFilter) {
      //SemanticListCompartment rv = NotationFactory.eINSTANCE.createSemanticListCompartment();
      //rv.setShowTitle(showTitle);
      //rv.setCollapsed(isCollapsed);
      Node rv;
      if (canCollapse) {
         rv = NotationFactory.eINSTANCE.createBasicCompartment();
      }
      else {
         rv = NotationFactory.eINSTANCE.createDecorationNode();
      }
      if (hasTitle) {
         TitleStyle ts = NotationFactory.eINSTANCE.createTitleStyle();
         ts.setShowTitle(true);
         rv.getStyles().add(ts);
      }
      if (canSort) {
         rv.getStyles().add(NotationFactory.eINSTANCE.createSortingStyle());
      }
      if (canFilter) {
         rv.getStyles().add(NotationFactory.eINSTANCE.createFilteringStyle());
      }
      rv.setType(hint);
      ViewUtil.insertChildView(owner, rv, ViewUtil.APPEND, true);
      return rv;
   }

   /**
    * @generated
    */
   private EObject getSemanticElement(IAdaptable semanticAdapter) {
      if (semanticAdapter == null) {
         return null;
      }
      EObject eObject = (EObject) semanticAdapter.getAdapter(EObject.class);
      if (eObject != null) {
         return EMFCoreUtil.resolve(TransactionUtil.getEditingDomain(eObject),
               eObject);
      }
      return null;
   }

   /**
    * @generated
    */
   private IElementType getSemanticElementType(IAdaptable semanticAdapter) {
      if (semanticAdapter == null) {
         return null;
      }
      return (IElementType) semanticAdapter.getAdapter(IElementType.class);
   }
}