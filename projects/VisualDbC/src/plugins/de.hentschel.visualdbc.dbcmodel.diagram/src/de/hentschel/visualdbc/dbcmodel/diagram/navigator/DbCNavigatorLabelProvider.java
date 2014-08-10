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

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import org.eclipse.gmf.runtime.common.ui.services.parser.IParser;
import org.eclipse.gmf.runtime.common.ui.services.parser.ParserOptions;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.jface.viewers.ITreePathLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.ViewerLabel;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.ICommonLabelProvider;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.AbstractDbcClassImplementsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeNameTypeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorSignatureEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceName2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodSignatureReturnTypeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractNameEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackage2EditPart;
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
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCParserProvider;

/**
 * @generated
 */
public class DbCNavigatorLabelProvider extends LabelProvider implements
      ICommonLabelProvider, ITreePathLabelProvider {

   /**
    * @generated
    */
   static {
      DbCDiagramEditorPlugin
            .getInstance()
            .getImageRegistry()
            .put("Navigator?UnknownElement", ImageDescriptor.getMissingImageDescriptor()); //$NON-NLS-1$
      DbCDiagramEditorPlugin
            .getInstance()
            .getImageRegistry()
            .put("Navigator?ImageNotFound", ImageDescriptor.getMissingImageDescriptor()); //$NON-NLS-1$
   }

   /**
    * @generated
    */
   public void updateLabel(ViewerLabel label, TreePath elementPath) {
      Object element = elementPath.getLastSegment();
      if (element instanceof DbCNavigatorItem
            && !isOwnView(((DbCNavigatorItem) element).getView())) {
         return;
      }
      label.setText(getText(element));
      label.setImage(getImage(element));
   }

   /**
    * @generated
    */
   public Image getImage(Object element) {
      if (element instanceof DbCNavigatorGroup) {
         DbCNavigatorGroup group = (DbCNavigatorGroup) element;
         return DbCDiagramEditorPlugin.getInstance().getBundledImage(
               group.getIcon());
      }

      if (element instanceof DbCNavigatorItem) {
         DbCNavigatorItem navigatorItem = (DbCNavigatorItem) element;
         if (!isOwnView(navigatorItem.getView())) {
            return super.getImage(element);
         }
         return getImage(navigatorItem.getView());
      }

      return super.getImage(element);
   }

   /**
    * @generated
    */
   public Image getImage(View view) {
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcPackage2EditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcPackage", DbCElementTypes.DbcPackage_3027); //$NON-NLS-1$
      case DbcInterfaceEditPart.VISUAL_ID:
         return getImage(
               "Navigator?TopLevelNode?http://www.hentschel.de/dbcmodel?DbcInterface", DbCElementTypes.DbcInterface_2011); //$NON-NLS-1$
      case DbcProofTargetEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Link?http://www.hentschel.de/dbcmodel?DbcProof?target", DbCElementTypes.DbcProofTarget_4001); //$NON-NLS-1$
      case DbcEnumEditPart.VISUAL_ID:
         return getImage(
               "Navigator?TopLevelNode?http://www.hentschel.de/dbcmodel?DbcEnum", DbCElementTypes.DbcEnum_2013); //$NON-NLS-1$
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcEnumLiteral", DbCElementTypes.DbcEnumLiteral_3020); //$NON-NLS-1$
      case DbcClassExtendsEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Link?http://www.hentschel.de/dbcmodel?DbcClass?extends", DbCElementTypes.DbcClassExtends_4003); //$NON-NLS-1$
      case DbcOperationContractEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcOperationContract", DbCElementTypes.DbcOperationContract_3026); //$NON-NLS-1$
      case DbcAttributeEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcAttribute", DbCElementTypes.DbcAttribute_3011); //$NON-NLS-1$
      case DbcInvariantEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcInvariant", DbCElementTypes.DbcInvariant_3035); //$NON-NLS-1$
      case DbcProofEditPart.VISUAL_ID:
         return getImage(
               "Navigator?TopLevelNode?http://www.hentschel.de/dbcmodel?DbcProof", DbCElementTypes.DbcProof_2014); //$NON-NLS-1$
      case DbcAxiomEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcAxiom", DbCElementTypes.DbcAxiom_3036); //$NON-NLS-1$
      case DbcClass2EditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcClass", DbCElementTypes.DbcClass_3031); //$NON-NLS-1$
      case DbcInterface2EditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcInterface", DbCElementTypes.DbcInterface_3032); //$NON-NLS-1$
      case DbcConstructorEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcConstructor", DbCElementTypes.DbcConstructor_3010); //$NON-NLS-1$
      case DbcClassEditPart.VISUAL_ID:
         return getImage(
               "Navigator?TopLevelNode?http://www.hentschel.de/dbcmodel?DbcClass", DbCElementTypes.DbcClass_2012); //$NON-NLS-1$
      case DbcProof2EditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcProof", DbCElementTypes.DbcProof_3034); //$NON-NLS-1$
      case DbcEnum2EditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcEnum", DbCElementTypes.DbcEnum_3033); //$NON-NLS-1$
      case DbCAxiomContractEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbCAxiomContract", DbCElementTypes.DbCAxiomContract_3037); //$NON-NLS-1$
      case DbcInterfaceExtendsEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Link?http://www.hentschel.de/dbcmodel?DbcInterface?extends", DbCElementTypes.DbcInterfaceExtends_4004); //$NON-NLS-1$
      case DbcModelEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Diagram?http://www.hentschel.de/dbcmodel?DbcModel", DbCElementTypes.DbcModel_1000); //$NON-NLS-1$
      case DbcProofReferenceEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Link?http://www.hentschel.de/dbcmodel?DbcProofReference", DbCElementTypes.DbcProofReference_4002); //$NON-NLS-1$
      case AbstractDbcClassImplementsEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Link?http://www.hentschel.de/dbcmodel?AbstractDbcClass?implements", DbCElementTypes.AbstractDbcClassImplements_4005); //$NON-NLS-1$
      case DbcPackageEditPart.VISUAL_ID:
         return getImage(
               "Navigator?TopLevelNode?http://www.hentschel.de/dbcmodel?DbcPackage", DbCElementTypes.DbcPackage_2007); //$NON-NLS-1$
      case DbcMethodEditPart.VISUAL_ID:
         return getImage(
               "Navigator?Node?http://www.hentschel.de/dbcmodel?DbcMethod", DbCElementTypes.DbcMethod_3009); //$NON-NLS-1$
      }
      return getImage("Navigator?UnknownElement", null); //$NON-NLS-1$
   }

   /**
    * @generated
    */
   private Image getImage(String key, IElementType elementType) {
      ImageRegistry imageRegistry = DbCDiagramEditorPlugin.getInstance()
            .getImageRegistry();
      Image image = imageRegistry.get(key);
      if (image == null && elementType != null
            && DbCElementTypes.isKnownElementType(elementType)) {
         image = DbCElementTypes.getImage(elementType);
         imageRegistry.put(key, image);
      }

      if (image == null) {
         image = imageRegistry.get("Navigator?ImageNotFound"); //$NON-NLS-1$
         imageRegistry.put(key, image);
      }
      return image;
   }

   /**
    * @generated
    */
   public String getText(Object element) {
      if (element instanceof DbCNavigatorGroup) {
         DbCNavigatorGroup group = (DbCNavigatorGroup) element;
         return group.getGroupName();
      }

      if (element instanceof DbCNavigatorItem) {
         DbCNavigatorItem navigatorItem = (DbCNavigatorItem) element;
         if (!isOwnView(navigatorItem.getView())) {
            return null;
         }
         return getText(navigatorItem.getView());
      }

      return super.getText(element);
   }

   /**
    * @generated
    */
   public String getText(View view) {
      if (view.getElement() != null && view.getElement().eIsProxy()) {
         return getUnresolvedDomainElementProxyText(view);
      }
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcPackage2EditPart.VISUAL_ID:
         return getDbcPackage_3027Text(view);
      case DbcInterfaceEditPart.VISUAL_ID:
         return getDbcInterface_2011Text(view);
      case DbcProofTargetEditPart.VISUAL_ID:
         return getDbcProofTarget_4001Text(view);
      case DbcEnumEditPart.VISUAL_ID:
         return getDbcEnum_2013Text(view);
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return getDbcEnumLiteral_3020Text(view);
      case DbcClassExtendsEditPart.VISUAL_ID:
         return getDbcClassExtends_4003Text(view);
      case DbcOperationContractEditPart.VISUAL_ID:
         return getDbcOperationContract_3026Text(view);
      case DbcAttributeEditPart.VISUAL_ID:
         return getDbcAttribute_3011Text(view);
      case DbcInvariantEditPart.VISUAL_ID:
         return getDbcInvariant_3035Text(view);
      case DbcProofEditPart.VISUAL_ID:
         return getDbcProof_2014Text(view);
      case DbcAxiomEditPart.VISUAL_ID:
         return getDbcAxiom_3036Text(view);
      case DbcClass2EditPart.VISUAL_ID:
         return getDbcClass_3031Text(view);
      case DbcInterface2EditPart.VISUAL_ID:
         return getDbcInterface_3032Text(view);
      case DbcConstructorEditPart.VISUAL_ID:
         return getDbcConstructor_3010Text(view);
      case DbcClassEditPart.VISUAL_ID:
         return getDbcClass_2012Text(view);
      case DbcProof2EditPart.VISUAL_ID:
         return getDbcProof_3034Text(view);
      case DbcEnum2EditPart.VISUAL_ID:
         return getDbcEnum_3033Text(view);
      case DbCAxiomContractEditPart.VISUAL_ID:
         return getDbCAxiomContract_3037Text(view);
      case DbcInterfaceExtendsEditPart.VISUAL_ID:
         return getDbcInterfaceExtends_4004Text(view);
      case DbcModelEditPart.VISUAL_ID:
         return getDbcModel_1000Text(view);
      case DbcProofReferenceEditPart.VISUAL_ID:
         return getDbcProofReference_4002Text(view);
      case AbstractDbcClassImplementsEditPart.VISUAL_ID:
         return getAbstractDbcClassImplements_4005Text(view);
      case DbcPackageEditPart.VISUAL_ID:
         return getDbcPackage_2007Text(view);
      case DbcMethodEditPart.VISUAL_ID:
         return getDbcMethod_3009Text(view);
      }
      return getUnknownElementText(view);
   }

   /**
    * @generated
    */
   private String getDbcClassExtends_4003Text(View view) {
      return ""; //$NON-NLS-1$
   }

   /**
    * @generated
    */
   private String getDbcInvariant_3035Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcInvariant_3035,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcInvariantNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5054); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcEnumLiteral_3020Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcEnumLiteral_3020,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcEnumLiteralNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5062); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcProof_2014Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcProof_2014,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcProofObligationEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5053); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbCAxiomContract_3037Text(View view) {
      IParser parser = DbCParserProvider
            .getParser(DbCElementTypes.DbCAxiomContract_3037,
                  view.getElement() != null ? view.getElement() : view,
                  DbCVisualIDRegistry
                        .getType(DbCAxiomContractNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5057); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcOperationContract_3026Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcOperationContract_3026,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry
                  .getType(DbcOperationContractNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5035); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcMethod_3009Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcMethod_3009,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry
                  .getType(DbcMethodSignatureReturnTypeEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5011); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcProof_3034Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcProof_3034,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcProofObligation2EditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5052); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcEnum_3033Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcEnum_3033,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcEnumName2EditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5046); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcPackage_3027Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcPackage_3027,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcPackageName2EditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5041); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcProofReference_4002Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcProofReference_4002,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry
                  .getType(DbcProofReferenceKindEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 6001); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcAxiom_3036Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcAxiom_3036,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcAxiomNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5056); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcEnum_2013Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcEnum_2013,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcEnumNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5051); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcAttribute_3011Text(View view) {
      IParser parser = DbCParserProvider
            .getParser(DbCElementTypes.DbcAttribute_3011,
                  view.getElement() != null ? view.getElement() : view,
                  DbCVisualIDRegistry
                        .getType(DbcAttributeNameTypeEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5061); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcConstructor_3010Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcConstructor_3010,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry
                  .getType(DbcConstructorSignatureEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5012); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcProofTarget_4001Text(View view) {
      return ""; //$NON-NLS-1$
   }

   /**
    * @generated
    */
   private String getDbcInterfaceExtends_4004Text(View view) {
      return ""; //$NON-NLS-1$
   }

   /**
    * @generated
    */
   private String getDbcInterface_2011Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcInterface_2011,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcInterfaceNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5049); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcInterface_3032Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcInterface_3032,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcInterfaceName2EditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5047); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcClass_3031Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcClass_3031,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcClassName2EditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5048); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcClass_2012Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcClass_2012,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcClassNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5050); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcPackage_2007Text(View view) {
      IParser parser = DbCParserProvider.getParser(
            DbCElementTypes.DbcPackage_2007,
            view.getElement() != null ? view.getElement() : view,
            DbCVisualIDRegistry.getType(DbcPackageNameEditPart.VISUAL_ID));
      if (parser != null) {
         return parser.getPrintString(new EObjectAdapter(
               view.getElement() != null ? view.getElement() : view),
               ParserOptions.NONE.intValue());
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Parser was not found for label " + 5042); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getDbcModel_1000Text(View view) {
      DbcModel domainModelElement = (DbcModel) view.getElement();
      if (domainModelElement != null) {
         return domainModelElement.getDriverId();
      }
      else {
         DbCDiagramEditorPlugin.getInstance().logError(
               "No domain element for view with visualID = " + 1000); //$NON-NLS-1$
         return ""; //$NON-NLS-1$
      }
   }

   /**
    * @generated
    */
   private String getAbstractDbcClassImplements_4005Text(View view) {
      return ""; //$NON-NLS-1$
   }

   /**
    * @generated
    */
   private String getUnknownElementText(View view) {
      return "<UnknownElement Visual_ID = " + view.getType() + ">"; //$NON-NLS-1$  //$NON-NLS-2$
   }

   /**
    * @generated
    */
   private String getUnresolvedDomainElementProxyText(View view) {
      return "<Unresolved domain element Visual_ID = " + view.getType() + ">"; //$NON-NLS-1$  //$NON-NLS-2$
   }

   /**
    * @generated
    */
   public void init(ICommonContentExtensionSite aConfig) {
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
   public String getDescription(Object anElement) {
      return null;
   }

   /**
    * @generated
    */
   private boolean isOwnView(View view) {
      return DbcModelEditPart.MODEL_ID.equals(DbCVisualIDRegistry
            .getModelID(view));
   }

}