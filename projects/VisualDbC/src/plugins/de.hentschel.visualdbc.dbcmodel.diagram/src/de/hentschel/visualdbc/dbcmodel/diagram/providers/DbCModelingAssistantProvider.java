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

package de.hentschel.visualdbc.dbcmodel.diagram.providers;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.emf.type.core.ElementTypeRegistry;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.ui.services.modelingassistant.ModelingAssistantProvider;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomDbcAxiomCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassDbcClassMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClassEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorDbcConstructorCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumDbcEnumMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceMainCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceDbcInterfaceMainCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterfaceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodDbcMethodCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartment2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcPackageDbcPackageCompartmentEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;
import de.hentschel.visualdbc.dbcmodel.diagram.part.Messages;

/**
 * @generated
 */
public class DbCModelingAssistantProvider extends ModelingAssistantProvider {

   /**
    * @generated
    */
   public List getTypesForPopupBar(IAdaptable host) {
      IGraphicalEditPart editPart = (IGraphicalEditPart) host
            .getAdapter(IGraphicalEditPart.class);
      if (editPart instanceof DbcModelEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(5);
         types.add(DbCElementTypes.DbcPackage_2007);
         types.add(DbCElementTypes.DbcInterface_2011);
         types.add(DbCElementTypes.DbcClass_2012);
         types.add(DbCElementTypes.DbcEnum_2013);
         types.add(DbCElementTypes.DbcProof_2014);
         return types;
      }
      if (editPart instanceof DbcInterfaceEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(1);
         types.add(DbCElementTypes.DbcAttribute_3011);
         return types;
      }
      if (editPart instanceof DbcClassEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(1);
         types.add(DbCElementTypes.DbcAttribute_3011);
         return types;
      }
      if (editPart instanceof DbcEnumEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(2);
         types.add(DbCElementTypes.DbcAttribute_3011);
         types.add(DbCElementTypes.DbcEnumLiteral_3020);
         return types;
      }
      if (editPart instanceof DbcClass2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(1);
         types.add(DbCElementTypes.DbcAttribute_3011);
         return types;
      }
      if (editPart instanceof DbcInterface2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(1);
         types.add(DbCElementTypes.DbcAttribute_3011);
         return types;
      }
      if (editPart instanceof DbcEnum2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(2);
         types.add(DbCElementTypes.DbcAttribute_3011);
         types.add(DbCElementTypes.DbcEnumLiteral_3020);
         return types;
      }
      if (editPart instanceof DbcPackageDbcPackageCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(5);
         types.add(DbCElementTypes.DbcPackage_3027);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcProof_3034);
         return types;
      }
      if (editPart instanceof DbcPackageDbcPackageCompartment2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(5);
         types.add(DbCElementTypes.DbcPackage_3027);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcProof_3034);
         return types;
      }
      if (editPart instanceof DbcClassDbcClassMainCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(8);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcConstructor_3010);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcAxiom_3036);
         return types;
      }
      if (editPart instanceof DbcInterfaceDbcInterfaceMainCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(7);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcAxiom_3036);
         return types;
      }
      if (editPart instanceof DbcEnumDbcEnumMainCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(8);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcConstructor_3010);
         types.add(DbCElementTypes.DbcAxiom_3036);
         return types;
      }
      if (editPart instanceof DbcMethodDbcMethodCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(2);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcOperationContract_3026);
         return types;
      }
      if (editPart instanceof DbcConstructorDbcConstructorCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(2);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcOperationContract_3026);
         return types;
      }
      if (editPart instanceof DbcAxiomDbcAxiomCompartmentEditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(1);
         types.add(DbCElementTypes.DbCAxiomContract_3037);
         return types;
      }
      if (editPart instanceof DbcInterfaceDbcInterfaceMainCompartment2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(7);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcAxiom_3036);
         return types;
      }
      if (editPart instanceof DbcClassDbcClassMainCompartment2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(8);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcConstructor_3010);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcAxiom_3036);
         return types;
      }
      if (editPart instanceof DbcEnumDbcEnumMainCompartment2EditPart) {
         ArrayList<IElementType> types = new ArrayList<IElementType>(8);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcProof_3034);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcConstructor_3010);
         types.add(DbCElementTypes.DbcAxiom_3036);
         return types;
      }
      return Collections.EMPTY_LIST;
   }

   /**
    * @generated
    */
   public List getRelTypesOnSource(IAdaptable source) {
      IGraphicalEditPart sourceEditPart = (IGraphicalEditPart) source
            .getAdapter(IGraphicalEditPart.class);
      if (sourceEditPart instanceof DbcInterfaceEditPart) {
         return ((DbcInterfaceEditPart) sourceEditPart).getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcClassEditPart) {
         return ((DbcClassEditPart) sourceEditPart).getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcEnumEditPart) {
         return ((DbcEnumEditPart) sourceEditPart).getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcProofEditPart) {
         return ((DbcProofEditPart) sourceEditPart).getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcClass2EditPart) {
         return ((DbcClass2EditPart) sourceEditPart).getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcInterface2EditPart) {
         return ((DbcInterface2EditPart) sourceEditPart)
               .getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcEnum2EditPart) {
         return ((DbcEnum2EditPart) sourceEditPart).getMARelTypesOnSource();
      }
      if (sourceEditPart instanceof DbcProof2EditPart) {
         return ((DbcProof2EditPart) sourceEditPart).getMARelTypesOnSource();
      }
      return Collections.EMPTY_LIST;
   }

   /**
    * @generated
    */
   public List getRelTypesOnTarget(IAdaptable target) {
      IGraphicalEditPart targetEditPart = (IGraphicalEditPart) target
            .getAdapter(IGraphicalEditPart.class);
      if (targetEditPart instanceof DbcInterfaceEditPart) {
         return ((DbcInterfaceEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcClassEditPart) {
         return ((DbcClassEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcEnumEditPart) {
         return ((DbcEnumEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcClass2EditPart) {
         return ((DbcClass2EditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcInterface2EditPart) {
         return ((DbcInterface2EditPart) targetEditPart)
               .getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcEnum2EditPart) {
         return ((DbcEnum2EditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcInvariantEditPart) {
         return ((DbcInvariantEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcAttributeEditPart) {
         return ((DbcAttributeEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcMethodEditPart) {
         return ((DbcMethodEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcOperationContractEditPart) {
         return ((DbcOperationContractEditPart) targetEditPart)
               .getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcConstructorEditPart) {
         return ((DbcConstructorEditPart) targetEditPart)
               .getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcEnumLiteralEditPart) {
         return ((DbcEnumLiteralEditPart) targetEditPart)
               .getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbcAxiomEditPart) {
         return ((DbcAxiomEditPart) targetEditPart).getMARelTypesOnTarget();
      }
      if (targetEditPart instanceof DbCAxiomContractEditPart) {
         return ((DbCAxiomContractEditPart) targetEditPart)
               .getMARelTypesOnTarget();
      }
      return Collections.EMPTY_LIST;
   }

   /**
    * @generated
    */
   public List getRelTypesOnSourceAndTarget(IAdaptable source, IAdaptable target) {
      IGraphicalEditPart sourceEditPart = (IGraphicalEditPart) source
            .getAdapter(IGraphicalEditPart.class);
      IGraphicalEditPart targetEditPart = (IGraphicalEditPart) target
            .getAdapter(IGraphicalEditPart.class);
      if (sourceEditPart instanceof DbcInterfaceEditPart) {
         return ((DbcInterfaceEditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcClassEditPart) {
         return ((DbcClassEditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcEnumEditPart) {
         return ((DbcEnumEditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcProofEditPart) {
         return ((DbcProofEditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcClass2EditPart) {
         return ((DbcClass2EditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcInterface2EditPart) {
         return ((DbcInterface2EditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcEnum2EditPart) {
         return ((DbcEnum2EditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      if (sourceEditPart instanceof DbcProof2EditPart) {
         return ((DbcProof2EditPart) sourceEditPart)
               .getMARelTypesOnSourceAndTarget(targetEditPart);
      }
      return Collections.EMPTY_LIST;
   }

   /**
    * @generated
    */
   public List getTypesForSource(IAdaptable target,
         IElementType relationshipType) {
      IGraphicalEditPart targetEditPart = (IGraphicalEditPart) target
            .getAdapter(IGraphicalEditPart.class);
      if (targetEditPart instanceof DbcInterfaceEditPart) {
         return ((DbcInterfaceEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcClassEditPart) {
         return ((DbcClassEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcEnumEditPart) {
         return ((DbcEnumEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcClass2EditPart) {
         return ((DbcClass2EditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcInterface2EditPart) {
         return ((DbcInterface2EditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcEnum2EditPart) {
         return ((DbcEnum2EditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcInvariantEditPart) {
         return ((DbcInvariantEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcAttributeEditPart) {
         return ((DbcAttributeEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcMethodEditPart) {
         return ((DbcMethodEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcOperationContractEditPart) {
         return ((DbcOperationContractEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcConstructorEditPart) {
         return ((DbcConstructorEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcEnumLiteralEditPart) {
         return ((DbcEnumLiteralEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbcAxiomEditPart) {
         return ((DbcAxiomEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      if (targetEditPart instanceof DbCAxiomContractEditPart) {
         return ((DbCAxiomContractEditPart) targetEditPart)
               .getMATypesForSource(relationshipType);
      }
      return Collections.EMPTY_LIST;
   }

   /**
    * @generated
    */
   public List getTypesForTarget(IAdaptable source,
         IElementType relationshipType) {
      IGraphicalEditPart sourceEditPart = (IGraphicalEditPart) source
            .getAdapter(IGraphicalEditPart.class);
      if (sourceEditPart instanceof DbcInterfaceEditPart) {
         return ((DbcInterfaceEditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcClassEditPart) {
         return ((DbcClassEditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcEnumEditPart) {
         return ((DbcEnumEditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcProofEditPart) {
         return ((DbcProofEditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcClass2EditPart) {
         return ((DbcClass2EditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcInterface2EditPart) {
         return ((DbcInterface2EditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcEnum2EditPart) {
         return ((DbcEnum2EditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      if (sourceEditPart instanceof DbcProof2EditPart) {
         return ((DbcProof2EditPart) sourceEditPart)
               .getMATypesForTarget(relationshipType);
      }
      return Collections.EMPTY_LIST;
   }

   /**
    * @generated
    */
   public EObject selectExistingElementForSource(IAdaptable target,
         IElementType relationshipType) {
      return selectExistingElement(target,
            getTypesForSource(target, relationshipType));
   }

   /**
    * @generated
    */
   public EObject selectExistingElementForTarget(IAdaptable source,
         IElementType relationshipType) {
      return selectExistingElement(source,
            getTypesForTarget(source, relationshipType));
   }

   /**
    * @generated
    */
   protected EObject selectExistingElement(IAdaptable host, Collection types) {
      if (types.isEmpty()) {
         return null;
      }
      IGraphicalEditPart editPart = (IGraphicalEditPart) host
            .getAdapter(IGraphicalEditPart.class);
      if (editPart == null) {
         return null;
      }
      Diagram diagram = (Diagram) editPart.getRoot().getContents().getModel();
      HashSet<EObject> elements = new HashSet<EObject>();
      for (Iterator<EObject> it = diagram.getElement().eAllContents(); it
            .hasNext();) {
         EObject element = it.next();
         if (isApplicableElement(element, types)) {
            elements.add(element);
         }
      }
      if (elements.isEmpty()) {
         return null;
      }
      return selectElement((EObject[]) elements.toArray(new EObject[elements
            .size()]));
   }

   /**
    * @generated
    */
   protected boolean isApplicableElement(EObject element, Collection types) {
      IElementType type = ElementTypeRegistry.getInstance().getElementType(
            element);
      return types.contains(type);
   }

   /**
    * @generated
    */
   protected EObject selectElement(EObject[] elements) {
      Shell shell = Display.getCurrent().getActiveShell();
      ILabelProvider labelProvider = new AdapterFactoryLabelProvider(
            DbCDiagramEditorPlugin.getInstance()
                  .getItemProvidersAdapterFactory());
      ElementListSelectionDialog dialog = new ElementListSelectionDialog(shell,
            labelProvider);
      dialog.setMessage(Messages.DbCModelingAssistantProviderMessage);
      dialog.setTitle(Messages.DbCModelingAssistantProviderTitle);
      dialog.setMultipleSelection(false);
      dialog.setElements(elements);
      EObject selected = null;
      if (dialog.open() == Window.OK) {
         selected = (EObject) dialog.getFirstResult();
      }
      return selected;
   }
}