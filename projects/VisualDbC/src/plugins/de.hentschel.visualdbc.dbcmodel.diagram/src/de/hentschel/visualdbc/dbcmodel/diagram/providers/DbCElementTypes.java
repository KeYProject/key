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

import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.ENamedElement;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.gmf.runtime.emf.type.core.ElementTypeRegistry;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.ImageRegistry;
import org.eclipse.swt.graphics.Image;

import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.AbstractDbcClassImplementsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceExtendsEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackage2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofTargetEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;

/**
 * @generated
 */
public class DbCElementTypes {

   /**
    * @generated
    */
   private DbCElementTypes() {
   }

   /**
    * @generated
    */
   private static Map<IElementType, ENamedElement> elements;

   /**
    * @generated
    */
   private static ImageRegistry imageRegistry;

   /**
    * @generated
    */
   private static Set<IElementType> KNOWN_ELEMENT_TYPES;

   /**
    * @generated
    */
   public static final IElementType DbcModel_1000 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcModel_1000"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcPackage_2007 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcPackage_2007"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcInterface_2011 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcInterface_2011"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcClass_2012 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcClass_2012"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcEnum_2013 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcEnum_2013"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcProof_2014 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcProof_2014"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcPackage_3027 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcPackage_3027"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcClass_3031 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcClass_3031"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcInterface_3032 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcInterface_3032"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcEnum_3033 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcEnum_3033"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcProof_3034 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcProof_3034"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcInvariant_3035 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcInvariant_3035"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcAttribute_3011 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcAttribute_3011"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcMethod_3009 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcMethod_3009"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcOperationContract_3026 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcOperationContract_3026"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcConstructor_3010 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcConstructor_3010"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcEnumLiteral_3020 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcEnumLiteral_3020"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcAxiom_3036 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcAxiom_3036"); //$NON-NLS-1$

   /**
    * @generated
    */
   public static final IElementType DbCAxiomContract_3037 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbCAxiomContract_3037"); //$NON-NLS-1$

   /**
    * @generated
    */
   public static final IElementType DbcProofTarget_4001 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcProofTarget_4001"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcProofReference_4002 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcProofReference_4002"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcClassExtends_4003 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcClassExtends_4003"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType DbcInterfaceExtends_4004 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.DbcInterfaceExtends_4004"); //$NON-NLS-1$
   /**
    * @generated
    */
   public static final IElementType AbstractDbcClassImplements_4005 = getElementType("de.hentschel.visualdbc.dbcmodel.diagram.AbstractDbcClassImplements_4005"); //$NON-NLS-1$

   /**
    * @generated
    */
   private static ImageRegistry getImageRegistry() {
      if (imageRegistry == null) {
         imageRegistry = new ImageRegistry();
      }
      return imageRegistry;
   }

   /**
    * @generated
    */
   private static String getImageRegistryKey(ENamedElement element) {
      return element.getName();
   }

   /**
    * @generated
    */
   private static ImageDescriptor getProvidedImageDescriptor(
         ENamedElement element) {
      if (element instanceof EStructuralFeature) {
         EStructuralFeature feature = ((EStructuralFeature) element);
         EClass eContainingClass = feature.getEContainingClass();
         EClassifier eType = feature.getEType();
         if (eContainingClass != null && !eContainingClass.isAbstract()) {
            element = eContainingClass;
         }
         else if (eType instanceof EClass && !((EClass) eType).isAbstract()) {
            element = eType;
         }
      }
      if (element instanceof EClass) {
         EClass eClass = (EClass) element;
         if (!eClass.isAbstract()) {
            return DbCDiagramEditorPlugin.getInstance().getItemImageDescriptor(
                  eClass.getEPackage().getEFactoryInstance().create(eClass));
         }
      }
      // TODO : support structural features
      return null;
   }

   /**
    * @generated
    */
   public static ImageDescriptor getImageDescriptor(ENamedElement element) {
      String key = getImageRegistryKey(element);
      ImageDescriptor imageDescriptor = getImageRegistry().getDescriptor(key);
      if (imageDescriptor == null) {
         imageDescriptor = getProvidedImageDescriptor(element);
         if (imageDescriptor == null) {
            imageDescriptor = ImageDescriptor.getMissingImageDescriptor();
         }
         getImageRegistry().put(key, imageDescriptor);
      }
      return imageDescriptor;
   }

   /**
    * @generated
    */
   public static Image getImage(ENamedElement element) {
      String key = getImageRegistryKey(element);
      Image image = getImageRegistry().get(key);
      if (image == null) {
         ImageDescriptor imageDescriptor = getProvidedImageDescriptor(element);
         if (imageDescriptor == null) {
            imageDescriptor = ImageDescriptor.getMissingImageDescriptor();
         }
         getImageRegistry().put(key, imageDescriptor);
         image = getImageRegistry().get(key);
      }
      return image;
   }

   /**
    * @generated
    */
   public static ImageDescriptor getImageDescriptor(IAdaptable hint) {
      ENamedElement element = getElement(hint);
      if (element == null) {
         return null;
      }
      return getImageDescriptor(element);
   }

   /**
    * @generated
    */
   public static Image getImage(IAdaptable hint) {
      ENamedElement element = getElement(hint);
      if (element == null) {
         return null;
      }
      return getImage(element);
   }

   /**
    * Returns 'type' of the ecore object associated with the hint.
    * 
    * @generated
    */
   public static ENamedElement getElement(IAdaptable hint) {
      Object type = hint.getAdapter(IElementType.class);
      if (elements == null) {
         elements = new IdentityHashMap<IElementType, ENamedElement>();

         elements.put(DbcModel_1000, DbcmodelPackage.eINSTANCE.getDbcModel());

         elements.put(DbcPackage_2007,
               DbcmodelPackage.eINSTANCE.getDbcPackage());

         elements.put(DbcInterface_2011,
               DbcmodelPackage.eINSTANCE.getDbcInterface());

         elements.put(DbcClass_2012, DbcmodelPackage.eINSTANCE.getDbcClass());

         elements.put(DbcEnum_2013, DbcmodelPackage.eINSTANCE.getDbcEnum());

         elements.put(DbcProof_2014, DbcmodelPackage.eINSTANCE.getDbcProof());

         elements.put(DbcPackage_3027,
               DbcmodelPackage.eINSTANCE.getDbcPackage());

         elements.put(DbcClass_3031, DbcmodelPackage.eINSTANCE.getDbcClass());

         elements.put(DbcInterface_3032,
               DbcmodelPackage.eINSTANCE.getDbcInterface());

         elements.put(DbcEnum_3033, DbcmodelPackage.eINSTANCE.getDbcEnum());

         elements.put(DbcProof_3034, DbcmodelPackage.eINSTANCE.getDbcProof());

         elements.put(DbcInvariant_3035,
               DbcmodelPackage.eINSTANCE.getDbcInvariant());

         elements.put(DbcAttribute_3011,
               DbcmodelPackage.eINSTANCE.getDbcAttribute());

         elements.put(DbcMethod_3009, DbcmodelPackage.eINSTANCE.getDbcMethod());

         elements.put(DbcOperationContract_3026,
               DbcmodelPackage.eINSTANCE.getDbcOperationContract());

         elements.put(DbcConstructor_3010,
               DbcmodelPackage.eINSTANCE.getDbcConstructor());

         elements.put(DbcEnumLiteral_3020,
               DbcmodelPackage.eINSTANCE.getDbcEnumLiteral());

         elements.put(DbcAxiom_3036, DbcmodelPackage.eINSTANCE.getDbcAxiom());

         elements.put(DbCAxiomContract_3037,
               DbcmodelPackage.eINSTANCE.getDbCAxiomContract());

         elements.put(DbcProofTarget_4001,
               DbcmodelPackage.eINSTANCE.getDbcProof_Target());

         elements.put(DbcProofReference_4002,
               DbcmodelPackage.eINSTANCE.getDbcProofReference());

         elements.put(DbcClassExtends_4003,
               DbcmodelPackage.eINSTANCE.getDbcClass_Extends());

         elements.put(DbcInterfaceExtends_4004,
               DbcmodelPackage.eINSTANCE.getDbcInterface_Extends());

         elements.put(AbstractDbcClassImplements_4005,
               DbcmodelPackage.eINSTANCE.getAbstractDbcClass_Implements());
      }
      return (ENamedElement) elements.get(type);
   }

   /**
    * @generated
    */
   private static IElementType getElementType(String id) {
      return ElementTypeRegistry.getInstance().getType(id);
   }

   /**
    * @generated
    */
   public static boolean isKnownElementType(IElementType elementType) {
      if (KNOWN_ELEMENT_TYPES == null) {
         KNOWN_ELEMENT_TYPES = new HashSet<IElementType>();
         KNOWN_ELEMENT_TYPES.add(DbcModel_1000);
         KNOWN_ELEMENT_TYPES.add(DbcPackage_2007);
         KNOWN_ELEMENT_TYPES.add(DbcInterface_2011);
         KNOWN_ELEMENT_TYPES.add(DbcClass_2012);
         KNOWN_ELEMENT_TYPES.add(DbcEnum_2013);
         KNOWN_ELEMENT_TYPES.add(DbcProof_2014);
         KNOWN_ELEMENT_TYPES.add(DbcPackage_3027);
         KNOWN_ELEMENT_TYPES.add(DbcClass_3031);
         KNOWN_ELEMENT_TYPES.add(DbcInterface_3032);
         KNOWN_ELEMENT_TYPES.add(DbcEnum_3033);
         KNOWN_ELEMENT_TYPES.add(DbcProof_3034);
         KNOWN_ELEMENT_TYPES.add(DbcInvariant_3035);
         KNOWN_ELEMENT_TYPES.add(DbcAttribute_3011);
         KNOWN_ELEMENT_TYPES.add(DbcMethod_3009);
         KNOWN_ELEMENT_TYPES.add(DbcOperationContract_3026);
         KNOWN_ELEMENT_TYPES.add(DbcConstructor_3010);
         KNOWN_ELEMENT_TYPES.add(DbcEnumLiteral_3020);
         KNOWN_ELEMENT_TYPES.add(DbcAxiom_3036);
         KNOWN_ELEMENT_TYPES.add(DbCAxiomContract_3037);
         KNOWN_ELEMENT_TYPES.add(DbcProofTarget_4001);
         KNOWN_ELEMENT_TYPES.add(DbcProofReference_4002);
         KNOWN_ELEMENT_TYPES.add(DbcClassExtends_4003);
         KNOWN_ELEMENT_TYPES.add(DbcInterfaceExtends_4004);
         KNOWN_ELEMENT_TYPES.add(AbstractDbcClassImplements_4005);
      }
      return KNOWN_ELEMENT_TYPES.contains(elementType);
   }

   /**
    * @generated
    */
   public static IElementType getElementType(int visualID) {
      switch (visualID) {
      case DbcModelEditPart.VISUAL_ID:
         return DbcModel_1000;
      case DbcPackageEditPart.VISUAL_ID:
         return DbcPackage_2007;
      case DbcInterfaceEditPart.VISUAL_ID:
         return DbcInterface_2011;
      case DbcClassEditPart.VISUAL_ID:
         return DbcClass_2012;
      case DbcEnumEditPart.VISUAL_ID:
         return DbcEnum_2013;
      case DbcProofEditPart.VISUAL_ID:
         return DbcProof_2014;
      case DbcPackage2EditPart.VISUAL_ID:
         return DbcPackage_3027;
      case DbcClass2EditPart.VISUAL_ID:
         return DbcClass_3031;
      case DbcInterface2EditPart.VISUAL_ID:
         return DbcInterface_3032;
      case DbcEnum2EditPart.VISUAL_ID:
         return DbcEnum_3033;
      case DbcProof2EditPart.VISUAL_ID:
         return DbcProof_3034;
      case DbcInvariantEditPart.VISUAL_ID:
         return DbcInvariant_3035;
      case DbcAttributeEditPart.VISUAL_ID:
         return DbcAttribute_3011;
      case DbcMethodEditPart.VISUAL_ID:
         return DbcMethod_3009;
      case DbcOperationContractEditPart.VISUAL_ID:
         return DbcOperationContract_3026;
      case DbcConstructorEditPart.VISUAL_ID:
         return DbcConstructor_3010;
      case DbcEnumLiteralEditPart.VISUAL_ID:
         return DbcEnumLiteral_3020;
      case DbcAxiomEditPart.VISUAL_ID:
         return DbcAxiom_3036;
      case DbCAxiomContractEditPart.VISUAL_ID:
         return DbCAxiomContract_3037;
      case DbcProofTargetEditPart.VISUAL_ID:
         return DbcProofTarget_4001;
      case DbcProofReferenceEditPart.VISUAL_ID:
         return DbcProofReference_4002;
      case DbcClassExtendsEditPart.VISUAL_ID:
         return DbcClassExtends_4003;
      case DbcInterfaceExtendsEditPart.VISUAL_ID:
         return DbcInterfaceExtends_4004;
      case AbstractDbcClassImplementsEditPart.VISUAL_ID:
         return AbstractDbcClassImplements_4005;
      }
      return null;
   }

}