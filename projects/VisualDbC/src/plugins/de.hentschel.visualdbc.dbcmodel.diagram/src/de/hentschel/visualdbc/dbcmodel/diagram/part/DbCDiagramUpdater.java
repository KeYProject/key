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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcClass;
import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.DbCAxiomContract;
import de.hentschel.visualdbc.dbcmodel.DbcAttribute;
import de.hentschel.visualdbc.dbcmodel.DbcAxiom;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcEnumLiteral;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcInvariant;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcPackage;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
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
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbCDiagramUpdater {

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getSemanticChildren(View view) {
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcModelEditPart.VISUAL_ID:
         return getDbcModel_1000SemanticChildren(view);
      case DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID:
         return getDbcPackageDbcPackageCompartment_7034SemanticChildren(view);
      case DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID:
         return getDbcPackageDbcPackageCompartment_7035SemanticChildren(view);
      case DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID:
         return getDbcClassDbcClassMainCompartment_7050SemanticChildren(view);
      case DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID:
         return getDbcClassDbcClassAttributeCompartment_7051SemanticChildren(view);
      case DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID:
         return getDbcInterfaceDbcInterfaceMainCompartment_7052SemanticChildren(view);
      case DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID:
         return getDbcInterfaceDbcInterfaceAttributeCompartment_7053SemanticChildren(view);
      case DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID:
         return getDbcEnumDbcEnumMainCompartment_7054SemanticChildren(view);
      case DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID:
         return getDbcEnumDbcEnumAttributeCompartment_7055SemanticChildren(view);
      case DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID:
         return getDbcEnumDbcEnumLiteralCompartment_7056SemanticChildren(view);
      case DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID:
         return getDbcMethodDbcMethodCompartment_7011SemanticChildren(view);
      case DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID:
         return getDbcConstructorDbcConstructorCompartment_7012SemanticChildren(view);
      case DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID:
         return getDbcAxiomDbcAxiomCompartment_7064SemanticChildren(view);
      case DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID:
         return getDbcInterfaceDbcInterfaceMainCompartment_7057SemanticChildren(view);
      case DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID:
         return getDbcInterfaceDbcInterfaceAttributeCompartment_7058SemanticChildren(view);
      case DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID:
         return getDbcClassDbcClassMainCompartment_7059SemanticChildren(view);
      case DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID:
         return getDbcClassDbcClassAttributeCompartment_7060SemanticChildren(view);
      case DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID:
         return getDbcEnumDbcEnumMainCompartment_7061SemanticChildren(view);
      case DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID:
         return getDbcEnumDbcEnumAttributeCompartment_7062SemanticChildren(view);
      case DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID:
         return getDbcEnumDbcEnumLiteralCompartment_7063SemanticChildren(view);
      }
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcModel_1000SemanticChildren(
         View view) {
      if (!view.isSetElement()) {
         return Collections.emptyList();
      }
      DbcModel modelElement = (DbcModel) view.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getPackages().iterator(); it.hasNext();) {
         DbcPackage childElement = (DbcPackage) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcPackageEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInterfaceEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcClassEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnumEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProofEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcPackageDbcPackageCompartment_7034SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcPackage modelElement = (DbcPackage) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getPackages().iterator(); it.hasNext();) {
         DbcPackage childElement = (DbcPackage) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcPackage2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcPackageDbcPackageCompartment_7035SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcPackage modelElement = (DbcPackage) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getPackages().iterator(); it.hasNext();) {
         DbcPackage childElement = (DbcPackage) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcPackage2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcClassDbcClassMainCompartment_7050SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcClass modelElement = (DbcClass) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getMethods().iterator(); it.hasNext();) {
         DbcMethod childElement = (DbcMethod) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcMethodEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getConstructors().iterator(); it
            .hasNext();) {
         DbcConstructor childElement = (DbcConstructor) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcConstructorEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getInvariants().iterator(); it
            .hasNext();) {
         DbcInvariant childElement = (DbcInvariant) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInvariantEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getAxioms().iterator(); it.hasNext();) {
         DbcAxiom childElement = (DbcAxiom) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAxiomEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcClassDbcClassAttributeCompartment_7051SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcClass modelElement = (DbcClass) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAttributes().iterator(); it
            .hasNext();) {
         DbcAttribute childElement = (DbcAttribute) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAttributeEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcInterfaceDbcInterfaceMainCompartment_7052SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcInterface modelElement = (DbcInterface) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getInvariants().iterator(); it
            .hasNext();) {
         DbcInvariant childElement = (DbcInvariant) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInvariantEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getMethods().iterator(); it.hasNext();) {
         DbcMethod childElement = (DbcMethod) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcMethodEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getAxioms().iterator(); it.hasNext();) {
         DbcAxiom childElement = (DbcAxiom) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAxiomEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcInterfaceDbcInterfaceAttributeCompartment_7053SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcInterface modelElement = (DbcInterface) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAttributes().iterator(); it
            .hasNext();) {
         DbcAttribute childElement = (DbcAttribute) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAttributeEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcEnumDbcEnumMainCompartment_7054SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcEnum modelElement = (DbcEnum) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getInvariants().iterator(); it
            .hasNext();) {
         DbcInvariant childElement = (DbcInvariant) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInvariantEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getMethods().iterator(); it.hasNext();) {
         DbcMethod childElement = (DbcMethod) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcMethodEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getConstructors().iterator(); it
            .hasNext();) {
         DbcConstructor childElement = (DbcConstructor) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcConstructorEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getAxioms().iterator(); it.hasNext();) {
         DbcAxiom childElement = (DbcAxiom) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAxiomEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcEnumDbcEnumAttributeCompartment_7055SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcEnum modelElement = (DbcEnum) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAttributes().iterator(); it
            .hasNext();) {
         DbcAttribute childElement = (DbcAttribute) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAttributeEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcEnumDbcEnumLiteralCompartment_7056SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcEnum modelElement = (DbcEnum) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getLiterals().iterator(); it.hasNext();) {
         DbcEnumLiteral childElement = (DbcEnumLiteral) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcEnumLiteralEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcMethodDbcMethodCompartment_7011SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcMethod modelElement = (DbcMethod) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getOperationContracts().iterator(); it
            .hasNext();) {
         DbcOperationContract childElement = (DbcOperationContract) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcOperationContractEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcConstructorDbcConstructorCompartment_7012SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcConstructor modelElement = (DbcConstructor) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getOperationContracts().iterator(); it
            .hasNext();) {
         DbcOperationContract childElement = (DbcOperationContract) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcOperationContractEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcAxiomDbcAxiomCompartment_7064SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcAxiom modelElement = (DbcAxiom) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAxiomContracts().iterator(); it
            .hasNext();) {
         DbCAxiomContract childElement = (DbCAxiomContract) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbCAxiomContractEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcInterfaceDbcInterfaceMainCompartment_7057SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcInterface modelElement = (DbcInterface) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getInvariants().iterator(); it
            .hasNext();) {
         DbcInvariant childElement = (DbcInvariant) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInvariantEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getMethods().iterator(); it.hasNext();) {
         DbcMethod childElement = (DbcMethod) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcMethodEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getAxioms().iterator(); it.hasNext();) {
         DbcAxiom childElement = (DbcAxiom) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAxiomEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcInterfaceDbcInterfaceAttributeCompartment_7058SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcInterface modelElement = (DbcInterface) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAttributes().iterator(); it
            .hasNext();) {
         DbcAttribute childElement = (DbcAttribute) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAttributeEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcClassDbcClassMainCompartment_7059SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcClass modelElement = (DbcClass) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getMethods().iterator(); it.hasNext();) {
         DbcMethod childElement = (DbcMethod) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcMethodEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getConstructors().iterator(); it
            .hasNext();) {
         DbcConstructor childElement = (DbcConstructor) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcConstructorEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getInvariants().iterator(); it
            .hasNext();) {
         DbcInvariant childElement = (DbcInvariant) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInvariantEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getAxioms().iterator(); it.hasNext();) {
         DbcAxiom childElement = (DbcAxiom) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAxiomEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcClassDbcClassAttributeCompartment_7060SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcClass modelElement = (DbcClass) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAttributes().iterator(); it
            .hasNext();) {
         DbcAttribute childElement = (DbcAttribute) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAttributeEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcEnumDbcEnumMainCompartment_7061SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcEnum modelElement = (DbcEnum) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getTypes().iterator(); it.hasNext();) {
         AbstractDbcType childElement = (AbstractDbcType) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcClass2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcInterface2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
         if (visualID == DbcEnum2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getProofs().iterator(); it.hasNext();) {
         DbcProof childElement = (DbcProof) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcProof2EditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getInvariants().iterator(); it
            .hasNext();) {
         DbcInvariant childElement = (DbcInvariant) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcInvariantEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getMethods().iterator(); it.hasNext();) {
         DbcMethod childElement = (DbcMethod) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcMethodEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getConstructors().iterator(); it
            .hasNext();) {
         DbcConstructor childElement = (DbcConstructor) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcConstructorEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      for (Iterator<?> it = modelElement.getAxioms().iterator(); it.hasNext();) {
         DbcAxiom childElement = (DbcAxiom) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAxiomEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcEnumDbcEnumAttributeCompartment_7062SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcEnum modelElement = (DbcEnum) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getAttributes().iterator(); it
            .hasNext();) {
         DbcAttribute childElement = (DbcAttribute) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcAttributeEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCNodeDescriptor> getDbcEnumDbcEnumLiteralCompartment_7063SemanticChildren(
         View view) {
      if (false == view.eContainer() instanceof View) {
         return Collections.emptyList();
      }
      View containerView = (View) view.eContainer();
      if (!containerView.isSetElement()) {
         return Collections.emptyList();
      }
      DbcEnum modelElement = (DbcEnum) containerView.getElement();
      LinkedList<DbCNodeDescriptor> result = new LinkedList<DbCNodeDescriptor>();
      for (Iterator<?> it = modelElement.getLiterals().iterator(); it.hasNext();) {
         DbcEnumLiteral childElement = (DbcEnumLiteral) it.next();
         int visualID = DbCVisualIDRegistry.getNodeVisualID(view, childElement);
         if (visualID == DbcEnumLiteralEditPart.VISUAL_ID) {
            result.add(new DbCNodeDescriptor(childElement, visualID));
            continue;
         }
      }
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getContainedLinks(View view) {
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcModelEditPart.VISUAL_ID:
         return getDbcModel_1000ContainedLinks(view);
      case DbcPackageEditPart.VISUAL_ID:
         return getDbcPackage_2007ContainedLinks(view);
      case DbcInterfaceEditPart.VISUAL_ID:
         return getDbcInterface_2011ContainedLinks(view);
      case DbcClassEditPart.VISUAL_ID:
         return getDbcClass_2012ContainedLinks(view);
      case DbcEnumEditPart.VISUAL_ID:
         return getDbcEnum_2013ContainedLinks(view);
      case DbcProofEditPart.VISUAL_ID:
         return getDbcProof_2014ContainedLinks(view);
      case DbcPackage2EditPart.VISUAL_ID:
         return getDbcPackage_3027ContainedLinks(view);
      case DbcClass2EditPart.VISUAL_ID:
         return getDbcClass_3031ContainedLinks(view);
      case DbcInterface2EditPart.VISUAL_ID:
         return getDbcInterface_3032ContainedLinks(view);
      case DbcEnum2EditPart.VISUAL_ID:
         return getDbcEnum_3033ContainedLinks(view);
      case DbcProof2EditPart.VISUAL_ID:
         return getDbcProof_3034ContainedLinks(view);
      case DbcInvariantEditPart.VISUAL_ID:
         return getDbcInvariant_3035ContainedLinks(view);
      case DbcAttributeEditPart.VISUAL_ID:
         return getDbcAttribute_3011ContainedLinks(view);
      case DbcMethodEditPart.VISUAL_ID:
         return getDbcMethod_3009ContainedLinks(view);
      case DbcOperationContractEditPart.VISUAL_ID:
         return getDbcOperationContract_3026ContainedLinks(view);
      case DbcConstructorEditPart.VISUAL_ID:
         return getDbcConstructor_3010ContainedLinks(view);
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return getDbcEnumLiteral_3020ContainedLinks(view);
      case DbcAxiomEditPart.VISUAL_ID:
         return getDbcAxiom_3036ContainedLinks(view);
      case DbCAxiomContractEditPart.VISUAL_ID:
         return getDbCAxiomContract_3037ContainedLinks(view);
      case DbcProofReferenceEditPart.VISUAL_ID:
         return getDbcProofReference_4002ContainedLinks(view);
      }
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getIncomingLinks(View view) {
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcPackageEditPart.VISUAL_ID:
         return getDbcPackage_2007IncomingLinks(view);
      case DbcInterfaceEditPart.VISUAL_ID:
         return getDbcInterface_2011IncomingLinks(view);
      case DbcClassEditPart.VISUAL_ID:
         return getDbcClass_2012IncomingLinks(view);
      case DbcEnumEditPart.VISUAL_ID:
         return getDbcEnum_2013IncomingLinks(view);
      case DbcProofEditPart.VISUAL_ID:
         return getDbcProof_2014IncomingLinks(view);
      case DbcPackage2EditPart.VISUAL_ID:
         return getDbcPackage_3027IncomingLinks(view);
      case DbcClass2EditPart.VISUAL_ID:
         return getDbcClass_3031IncomingLinks(view);
      case DbcInterface2EditPart.VISUAL_ID:
         return getDbcInterface_3032IncomingLinks(view);
      case DbcEnum2EditPart.VISUAL_ID:
         return getDbcEnum_3033IncomingLinks(view);
      case DbcProof2EditPart.VISUAL_ID:
         return getDbcProof_3034IncomingLinks(view);
      case DbcInvariantEditPart.VISUAL_ID:
         return getDbcInvariant_3035IncomingLinks(view);
      case DbcAttributeEditPart.VISUAL_ID:
         return getDbcAttribute_3011IncomingLinks(view);
      case DbcMethodEditPart.VISUAL_ID:
         return getDbcMethod_3009IncomingLinks(view);
      case DbcOperationContractEditPart.VISUAL_ID:
         return getDbcOperationContract_3026IncomingLinks(view);
      case DbcConstructorEditPart.VISUAL_ID:
         return getDbcConstructor_3010IncomingLinks(view);
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return getDbcEnumLiteral_3020IncomingLinks(view);
      case DbcAxiomEditPart.VISUAL_ID:
         return getDbcAxiom_3036IncomingLinks(view);
      case DbCAxiomContractEditPart.VISUAL_ID:
         return getDbCAxiomContract_3037IncomingLinks(view);
      case DbcProofReferenceEditPart.VISUAL_ID:
         return getDbcProofReference_4002IncomingLinks(view);
      }
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getOutgoingLinks(View view) {
      switch (DbCVisualIDRegistry.getVisualID(view)) {
      case DbcPackageEditPart.VISUAL_ID:
         return getDbcPackage_2007OutgoingLinks(view);
      case DbcInterfaceEditPart.VISUAL_ID:
         return getDbcInterface_2011OutgoingLinks(view);
      case DbcClassEditPart.VISUAL_ID:
         return getDbcClass_2012OutgoingLinks(view);
      case DbcEnumEditPart.VISUAL_ID:
         return getDbcEnum_2013OutgoingLinks(view);
      case DbcProofEditPart.VISUAL_ID:
         return getDbcProof_2014OutgoingLinks(view);
      case DbcPackage2EditPart.VISUAL_ID:
         return getDbcPackage_3027OutgoingLinks(view);
      case DbcClass2EditPart.VISUAL_ID:
         return getDbcClass_3031OutgoingLinks(view);
      case DbcInterface2EditPart.VISUAL_ID:
         return getDbcInterface_3032OutgoingLinks(view);
      case DbcEnum2EditPart.VISUAL_ID:
         return getDbcEnum_3033OutgoingLinks(view);
      case DbcProof2EditPart.VISUAL_ID:
         return getDbcProof_3034OutgoingLinks(view);
      case DbcInvariantEditPart.VISUAL_ID:
         return getDbcInvariant_3035OutgoingLinks(view);
      case DbcAttributeEditPart.VISUAL_ID:
         return getDbcAttribute_3011OutgoingLinks(view);
      case DbcMethodEditPart.VISUAL_ID:
         return getDbcMethod_3009OutgoingLinks(view);
      case DbcOperationContractEditPart.VISUAL_ID:
         return getDbcOperationContract_3026OutgoingLinks(view);
      case DbcConstructorEditPart.VISUAL_ID:
         return getDbcConstructor_3010OutgoingLinks(view);
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return getDbcEnumLiteral_3020OutgoingLinks(view);
      case DbcAxiomEditPart.VISUAL_ID:
         return getDbcAxiom_3036OutgoingLinks(view);
      case DbCAxiomContractEditPart.VISUAL_ID:
         return getDbCAxiomContract_3037OutgoingLinks(view);
      case DbcProofReferenceEditPart.VISUAL_ID:
         return getDbcProofReference_4002OutgoingLinks(view);
      }
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcModel_1000ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcPackage_2007ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInterface_2011ContainedLinks(
         View view) {
      DbcInterface modelElement = (DbcInterface) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcInterface_Extends_4004(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcClass_2012ContainedLinks(
         View view) {
      DbcClass modelElement = (DbcClass) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcClass_Extends_4003(modelElement));
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnum_2013ContainedLinks(View view) {
      DbcEnum modelElement = (DbcEnum) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProof_2014ContainedLinks(
         View view) {
      DbcProof modelElement = (DbcProof) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcProof_Target_4001(modelElement));
      result.addAll(getContainedTypeModelFacetLinks_DbcProofReference_4002(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcPackage_3027ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcClass_3031ContainedLinks(
         View view) {
      DbcClass modelElement = (DbcClass) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcClass_Extends_4003(modelElement));
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInterface_3032ContainedLinks(
         View view) {
      DbcInterface modelElement = (DbcInterface) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcInterface_Extends_4004(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnum_3033ContainedLinks(View view) {
      DbcEnum modelElement = (DbcEnum) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProof_3034ContainedLinks(
         View view) {
      DbcProof modelElement = (DbcProof) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcProof_Target_4001(modelElement));
      result.addAll(getContainedTypeModelFacetLinks_DbcProofReference_4002(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInvariant_3035ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcAttribute_3011ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcMethod_3009ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcOperationContract_3026ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcConstructor_3010ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnumLiteral_3020ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcAxiom_3036ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbCAxiomContract_3037ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProofReference_4002ContainedLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcPackage_2007IncomingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInterface_2011IncomingLinks(
         View view) {
      DbcInterface modelElement = (DbcInterface) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      result.addAll(getIncomingFeatureModelFacetLinks_DbcInterface_Extends_4004(
            modelElement, crossReferences));
      result.addAll(getIncomingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcClass_2012IncomingLinks(View view) {
      DbcClass modelElement = (DbcClass) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      result.addAll(getIncomingFeatureModelFacetLinks_DbcClass_Extends_4003(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnum_2013IncomingLinks(View view) {
      DbcEnum modelElement = (DbcEnum) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProof_2014IncomingLinks(View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcPackage_3027IncomingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcClass_3031IncomingLinks(View view) {
      DbcClass modelElement = (DbcClass) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      result.addAll(getIncomingFeatureModelFacetLinks_DbcClass_Extends_4003(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInterface_3032IncomingLinks(
         View view) {
      DbcInterface modelElement = (DbcInterface) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      result.addAll(getIncomingFeatureModelFacetLinks_DbcInterface_Extends_4004(
            modelElement, crossReferences));
      result.addAll(getIncomingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnum_3033IncomingLinks(View view) {
      DbcEnum modelElement = (DbcEnum) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProof_3034IncomingLinks(View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInvariant_3035IncomingLinks(
         View view) {
      DbcInvariant modelElement = (DbcInvariant) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcAttribute_3011IncomingLinks(
         View view) {
      DbcAttribute modelElement = (DbcAttribute) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcMethod_3009IncomingLinks(
         View view) {
      DbcMethod modelElement = (DbcMethod) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcOperationContract_3026IncomingLinks(
         View view) {
      DbcOperationContract modelElement = (DbcOperationContract) view
            .getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcConstructor_3010IncomingLinks(
         View view) {
      DbcConstructor modelElement = (DbcConstructor) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnumLiteral_3020IncomingLinks(
         View view) {
      DbcEnumLiteral modelElement = (DbcEnumLiteral) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcAxiom_3036IncomingLinks(View view) {
      DbcAxiom modelElement = (DbcAxiom) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbCAxiomContract_3037IncomingLinks(
         View view) {
      DbCAxiomContract modelElement = (DbCAxiomContract) view.getElement();
      Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences = EcoreUtil.CrossReferencer
            .find(view.eResource().getResourceSet().getResources());
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
            modelElement, crossReferences));
      result.addAll(getIncomingTypeModelFacetLinks_DbcProofReference_4002(
            modelElement, crossReferences));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProofReference_4002IncomingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcPackage_2007OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInterface_2011OutgoingLinks(
         View view) {
      DbcInterface modelElement = (DbcInterface) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcInterface_Extends_4004(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcClass_2012OutgoingLinks(View view) {
      DbcClass modelElement = (DbcClass) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcClass_Extends_4003(modelElement));
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnum_2013OutgoingLinks(View view) {
      DbcEnum modelElement = (DbcEnum) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProof_2014OutgoingLinks(View view) {
      DbcProof modelElement = (DbcProof) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcProof_Target_4001(modelElement));
      result.addAll(getContainedTypeModelFacetLinks_DbcProofReference_4002(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcPackage_3027OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcClass_3031OutgoingLinks(View view) {
      DbcClass modelElement = (DbcClass) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcClass_Extends_4003(modelElement));
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInterface_3032OutgoingLinks(
         View view) {
      DbcInterface modelElement = (DbcInterface) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcInterface_Extends_4004(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnum_3033OutgoingLinks(View view) {
      DbcEnum modelElement = (DbcEnum) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProof_3034OutgoingLinks(View view) {
      DbcProof modelElement = (DbcProof) view.getElement();
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      result.addAll(getOutgoingFeatureModelFacetLinks_DbcProof_Target_4001(modelElement));
      result.addAll(getContainedTypeModelFacetLinks_DbcProofReference_4002(modelElement));
      return result;
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcInvariant_3035OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcAttribute_3011OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcMethod_3009OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcOperationContract_3026OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcConstructor_3010OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcEnumLiteral_3020OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcAxiom_3036OutgoingLinks(View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbCAxiomContract_3037OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   public static List<DbCLinkDescriptor> getDbcProofReference_4002OutgoingLinks(
         View view) {
      return Collections.emptyList();
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getContainedTypeModelFacetLinks_DbcProofReference_4002(
         DbcProof container) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      for (Iterator<?> links = container.getProofReferences().iterator(); links
            .hasNext();) {
         EObject linkObject = (EObject) links.next();
         if (false == linkObject instanceof DbcProofReference) {
            continue;
         }
         DbcProofReference link = (DbcProofReference) linkObject;
         if (DbcProofReferenceEditPart.VISUAL_ID != DbCVisualIDRegistry
               .getLinkWithClassVisualID(link)) {
            continue;
         }
         IDbCProofReferencable dst = link.getTarget();
         result.add(new DbCLinkDescriptor(container, dst, link,
               DbCElementTypes.DbcProofReference_4002,
               DbcProofReferenceEditPart.VISUAL_ID));
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getIncomingFeatureModelFacetLinks_DbcProof_Target_4001(
         IDbCProvable target,
         Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      Collection<EStructuralFeature.Setting> settings = crossReferences
            .get(target);
      for (EStructuralFeature.Setting setting : settings) {
         if (setting.getEStructuralFeature() == DbcmodelPackage.eINSTANCE
               .getDbcProof_Target()) {
            result.add(new DbCLinkDescriptor(setting.getEObject(), target,
                  DbCElementTypes.DbcProofTarget_4001,
                  DbcProofTargetEditPart.VISUAL_ID));
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getIncomingTypeModelFacetLinks_DbcProofReference_4002(
         IDbCProofReferencable target,
         Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      Collection<EStructuralFeature.Setting> settings = crossReferences
            .get(target);
      for (EStructuralFeature.Setting setting : settings) {
         if (setting.getEStructuralFeature() != DbcmodelPackage.eINSTANCE
               .getDbcProofReference_Target()
               || false == setting.getEObject() instanceof DbcProofReference) {
            continue;
         }
         DbcProofReference link = (DbcProofReference) setting.getEObject();
         if (DbcProofReferenceEditPart.VISUAL_ID != DbCVisualIDRegistry
               .getLinkWithClassVisualID(link)) {
            continue;
         }
         if (false == link.eContainer() instanceof DbcProof) {
            continue;
         }
         DbcProof container = (DbcProof) link.eContainer();
         result.add(new DbCLinkDescriptor(container, target, link,
               DbCElementTypes.DbcProofReference_4002,
               DbcProofReferenceEditPart.VISUAL_ID));

      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getIncomingFeatureModelFacetLinks_DbcClass_Extends_4003(
         DbcClass target,
         Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      Collection<EStructuralFeature.Setting> settings = crossReferences
            .get(target);
      for (EStructuralFeature.Setting setting : settings) {
         if (setting.getEStructuralFeature() == DbcmodelPackage.eINSTANCE
               .getDbcClass_Extends()) {
            result.add(new DbCLinkDescriptor(setting.getEObject(), target,
                  DbCElementTypes.DbcClassExtends_4003,
                  DbcClassExtendsEditPart.VISUAL_ID));
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getIncomingFeatureModelFacetLinks_DbcInterface_Extends_4004(
         DbcInterface target,
         Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      Collection<EStructuralFeature.Setting> settings = crossReferences
            .get(target);
      for (EStructuralFeature.Setting setting : settings) {
         if (setting.getEStructuralFeature() == DbcmodelPackage.eINSTANCE
               .getDbcInterface_Extends()) {
            result.add(new DbCLinkDescriptor(setting.getEObject(), target,
                  DbCElementTypes.DbcInterfaceExtends_4004,
                  DbcInterfaceExtendsEditPart.VISUAL_ID));
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getIncomingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(
         DbcInterface target,
         Map<EObject, Collection<EStructuralFeature.Setting>> crossReferences) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      Collection<EStructuralFeature.Setting> settings = crossReferences
            .get(target);
      for (EStructuralFeature.Setting setting : settings) {
         if (setting.getEStructuralFeature() == DbcmodelPackage.eINSTANCE
               .getAbstractDbcClass_Implements()) {
            result.add(new DbCLinkDescriptor(setting.getEObject(), target,
                  DbCElementTypes.AbstractDbcClassImplements_4005,
                  AbstractDbcClassImplementsEditPart.VISUAL_ID));
         }
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getOutgoingFeatureModelFacetLinks_DbcProof_Target_4001(
         DbcProof source) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      IDbCProvable destination = source.getTarget();
      if (destination == null) {
         return result;
      }
      result.add(new DbCLinkDescriptor(source, destination,
            DbCElementTypes.DbcProofTarget_4001,
            DbcProofTargetEditPart.VISUAL_ID));
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getOutgoingFeatureModelFacetLinks_DbcClass_Extends_4003(
         DbcClass source) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      for (Iterator<?> destinations = source.getExtends().iterator(); destinations
            .hasNext();) {
         DbcClass destination = (DbcClass) destinations.next();
         result.add(new DbCLinkDescriptor(source, destination,
               DbCElementTypes.DbcClassExtends_4003,
               DbcClassExtendsEditPart.VISUAL_ID));
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getOutgoingFeatureModelFacetLinks_DbcInterface_Extends_4004(
         DbcInterface source) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      for (Iterator<?> destinations = source.getExtends().iterator(); destinations
            .hasNext();) {
         DbcInterface destination = (DbcInterface) destinations.next();
         result.add(new DbCLinkDescriptor(source, destination,
               DbCElementTypes.DbcInterfaceExtends_4004,
               DbcInterfaceExtendsEditPart.VISUAL_ID));
      }
      return result;
   }

   /**
    * @generated
    */
   private static Collection<DbCLinkDescriptor> getOutgoingFeatureModelFacetLinks_AbstractDbcClass_Implements_4005(
         AbstractDbcClass source) {
      LinkedList<DbCLinkDescriptor> result = new LinkedList<DbCLinkDescriptor>();
      for (Iterator<?> destinations = source.getImplements().iterator(); destinations
            .hasNext();) {
         DbcInterface destination = (DbcInterface) destinations.next();
         result.add(new DbCLinkDescriptor(source, destination,
               DbCElementTypes.AbstractDbcClassImplements_4005,
               AbstractDbcClassImplementsEditPart.VISUAL_ID));
      }
      return result;
   }

}