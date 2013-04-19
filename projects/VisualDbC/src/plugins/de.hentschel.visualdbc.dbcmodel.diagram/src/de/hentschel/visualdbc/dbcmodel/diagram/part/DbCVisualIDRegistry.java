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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import org.eclipse.core.runtime.Platform;
import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
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

/**
 * This registry is used to determine which type of visual object should be
 * created for the corresponding Diagram, Node, ChildNode or Link represented
 * by a domain model object.
 * 
 * @generated
 */
public class DbCVisualIDRegistry {

   /**
    * @generated
    */
   private static final String DEBUG_KEY = "de.hentschel.visualdbc.dbcmodel.diagram/debug/visualID"; //$NON-NLS-1$

   /**
    * @generated
    */
   public static int getVisualID(View view) {
      if (view instanceof Diagram) {
         if (DbcModelEditPart.MODEL_ID.equals(view.getType())) {
            return DbcModelEditPart.VISUAL_ID;
         }
         else {
            return -1;
         }
      }
      return de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry
            .getVisualID(view.getType());
   }

   /**
    * @generated
    */
   public static String getModelID(View view) {
      View diagram = view.getDiagram();
      while (view != diagram) {
         EAnnotation annotation = view.getEAnnotation("Shortcut"); //$NON-NLS-1$
         if (annotation != null) {
            return (String) annotation.getDetails().get("modelID"); //$NON-NLS-1$
         }
         view = (View) view.eContainer();
      }
      return diagram != null ? diagram.getType() : null;
   }

   /**
    * @generated
    */
   public static int getVisualID(String type) {
      try {
         return Integer.parseInt(type);
      }
      catch (NumberFormatException e) {
         if (Boolean.TRUE.toString().equalsIgnoreCase(
               Platform.getDebugOption(DEBUG_KEY))) {
            DbCDiagramEditorPlugin.getInstance().logError(
                  "Unable to parse view type as a visualID number: " + type);
         }
      }
      return -1;
   }

   /**
    * @generated
    */
   public static String getType(int visualID) {
      return Integer.toString(visualID);
   }

   /**
    * @generated
    */
   public static int getDiagramVisualID(EObject domainElement) {
      if (domainElement == null) {
         return -1;
      }
      if (DbcmodelPackage.eINSTANCE.getDbcModel().isSuperTypeOf(
            domainElement.eClass())
            && isDiagram((DbcModel) domainElement)) {
         return DbcModelEditPart.VISUAL_ID;
      }
      return -1;
   }

   /**
    * @generated
    */
   public static int getNodeVisualID(View containerView, EObject domainElement) {
      if (domainElement == null) {
         return -1;
      }
      String containerModelID = de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry
            .getModelID(containerView);
      if (!DbcModelEditPart.MODEL_ID.equals(containerModelID)) {
         return -1;
      }
      int containerVisualID;
      if (DbcModelEditPart.MODEL_ID.equals(containerModelID)) {
         containerVisualID = de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry
               .getVisualID(containerView);
      }
      else {
         if (containerView instanceof Diagram) {
            containerVisualID = DbcModelEditPart.VISUAL_ID;
         }
         else {
            return -1;
         }
      }
      switch (containerVisualID) {
      case DbcModelEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcPackage().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcPackageEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterfaceEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClassEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnumEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProofEditPart.VISUAL_ID;
         }
         break;
      case DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcPackage().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcPackage2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         break;
      case DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcPackage().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcPackage2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         break;
      case DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcMethod().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcMethodEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcConstructor().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcConstructorEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInvariant().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInvariantEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcAxiom().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAxiomEditPart.VISUAL_ID;
         }
         break;
      case DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcAttribute().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAttributeEditPart.VISUAL_ID;
         }
         break;
      case DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInvariant().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInvariantEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcMethod().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcMethodEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcAxiom().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAxiomEditPart.VISUAL_ID;
         }
         break;
      case DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcAttribute().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAttributeEditPart.VISUAL_ID;
         }
         break;
      case DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInvariant().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInvariantEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcMethod().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcMethodEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcConstructor().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcConstructorEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcAxiom().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAxiomEditPart.VISUAL_ID;
         }
         break;
      case DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcAttribute().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAttributeEditPart.VISUAL_ID;
         }
         break;
      case DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcEnumLiteral().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnumLiteralEditPart.VISUAL_ID;
         }
         break;
      case DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcOperationContract().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcOperationContractEditPart.VISUAL_ID;
         }
         break;
      case DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcOperationContract().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcOperationContractEditPart.VISUAL_ID;
         }
         break;
      case DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbCAxiomContract().isSuperTypeOf(
               domainElement.eClass())) {
            return DbCAxiomContractEditPart.VISUAL_ID;
         }
         break;
      case DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInvariant().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInvariantEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcMethod().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcMethodEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcAxiom().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAxiomEditPart.VISUAL_ID;
         }
         break;
      case DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcAttribute().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAttributeEditPart.VISUAL_ID;
         }
         break;
      case DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcMethod().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcMethodEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcConstructor().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcConstructorEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInvariant().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInvariantEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcAxiom().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAxiomEditPart.VISUAL_ID;
         }
         break;
      case DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcAttribute().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAttributeEditPart.VISUAL_ID;
         }
         break;
      case DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcClass().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcClass2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInterface().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInterface2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcEnum().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnum2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcProof().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcProof2EditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcInvariant().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcInvariantEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcMethod().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcMethodEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcConstructor().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcConstructorEditPart.VISUAL_ID;
         }
         if (DbcmodelPackage.eINSTANCE.getDbcAxiom().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAxiomEditPart.VISUAL_ID;
         }
         break;
      case DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcAttribute().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcAttributeEditPart.VISUAL_ID;
         }
         break;
      case DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID:
         if (DbcmodelPackage.eINSTANCE.getDbcEnumLiteral().isSuperTypeOf(
               domainElement.eClass())) {
            return DbcEnumLiteralEditPart.VISUAL_ID;
         }
         break;
      }
      return -1;
   }

   /**
    * @generated
    */
   public static boolean canCreateNode(View containerView, int nodeVisualID) {
      String containerModelID = de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry
            .getModelID(containerView);
      if (!DbcModelEditPart.MODEL_ID.equals(containerModelID)) {
         return false;
      }
      int containerVisualID;
      if (DbcModelEditPart.MODEL_ID.equals(containerModelID)) {
         containerVisualID = de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry
               .getVisualID(containerView);
      }
      else {
         if (containerView instanceof Diagram) {
            containerVisualID = DbcModelEditPart.VISUAL_ID;
         }
         else {
            return false;
         }
      }
      switch (containerVisualID) {
      case DbcModelEditPart.VISUAL_ID:
         if (DbcPackageEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterfaceEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClassEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProofEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcPackageEditPart.VISUAL_ID:
         if (DbcPackageNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInterfaceEditPart.VISUAL_ID:
         if (DbcInterfaceNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcClassEditPart.VISUAL_ID:
         if (DbcClassNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumEditPart.VISUAL_ID:
         if (DbcEnumNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcProofEditPart.VISUAL_ID:
         if (DbcProofObligationEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcPackage2EditPart.VISUAL_ID:
         if (DbcPackageName2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcClass2EditPart.VISUAL_ID:
         if (DbcClassName2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInterface2EditPart.VISUAL_ID:
         if (DbcInterfaceName2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnum2EditPart.VISUAL_ID:
         if (DbcEnumName2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcProof2EditPart.VISUAL_ID:
         if (DbcProofObligation2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInvariantEditPart.VISUAL_ID:
         if (DbcInvariantNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantTextEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcAttributeEditPart.VISUAL_ID:
         if (DbcAttributeNameTypeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcMethodEditPart.VISUAL_ID:
         if (DbcMethodSignatureReturnTypeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcOperationContractEditPart.VISUAL_ID:
         if (DbcOperationContractNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcOperationContractPreEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcOperationContractPostEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcConstructorEditPart.VISUAL_ID:
         if (DbcConstructorSignatureEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumLiteralEditPart.VISUAL_ID:
         if (DbcEnumLiteralNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcAxiomEditPart.VISUAL_ID:
         if (DbcAxiomNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomDefinitionEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbCAxiomContractEditPart.VISUAL_ID:
         if (DbCAxiomContractNameEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbCAxiomContractPreEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbCAxiomContractDepEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID:
         if (DbcPackage2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID:
         if (DbcPackage2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID:
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcConstructorEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID:
         if (DbcAttributeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID:
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID:
         if (DbcAttributeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID:
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcConstructorEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID:
         if (DbcAttributeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID:
         if (DbcEnumLiteralEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID:
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcOperationContractEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID:
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcOperationContractEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID:
         if (DbCAxiomContractEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID:
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID:
         if (DbcAttributeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID:
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcConstructorEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID:
         if (DbcAttributeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID:
         if (DbcClass2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInterface2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcEnum2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcProof2EditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcInvariantEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcMethodEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcConstructorEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         if (DbcAxiomEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID:
         if (DbcAttributeEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID:
         if (DbcEnumLiteralEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      case DbcProofReferenceEditPart.VISUAL_ID:
         if (DbcProofReferenceKindEditPart.VISUAL_ID == nodeVisualID) {
            return true;
         }
         break;
      }
      return false;
   }

   /**
    * @generated
    */
   public static int getLinkWithClassVisualID(EObject domainElement) {
      if (domainElement == null) {
         return -1;
      }
      if (DbcmodelPackage.eINSTANCE.getDbcProofReference().isSuperTypeOf(
            domainElement.eClass())) {
         return DbcProofReferenceEditPart.VISUAL_ID;
      }
      return -1;
   }

   /**
    * User can change implementation of this method to handle some specific
    * situations not covered by default logic.
    * 
    * @generated
    */
   private static boolean isDiagram(DbcModel element) {
      return true;
   }

}