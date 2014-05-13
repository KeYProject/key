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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.parts;

import org.eclipse.draw2d.FigureUtilities;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartFactory;
import org.eclipse.gef.tools.CellEditorLocator;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITextAwareEditPart;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Text;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbCEditPartFactory implements EditPartFactory {

   /**
    * @generated
    */
   public EditPart createEditPart(EditPart context, Object model) {
      if (model instanceof View) {
         View view = (View) model;
         switch (DbCVisualIDRegistry.getVisualID(view)) {

         case DbcModelEditPart.VISUAL_ID:
            return new DbcModelEditPart(view);

         case DbcPackageEditPart.VISUAL_ID:
            return new DbcPackageEditPart(view);

         case DbcPackageNameEditPart.VISUAL_ID:
            return new DbcPackageNameEditPart(view);

         case DbcInterfaceEditPart.VISUAL_ID:
            return new DbcInterfaceEditPart(view);

         case DbcInterfaceNameEditPart.VISUAL_ID:
            return new DbcInterfaceNameEditPart(view);

         case DbcClassEditPart.VISUAL_ID:
            return new DbcClassEditPart(view);

         case DbcClassNameEditPart.VISUAL_ID:
            return new DbcClassNameEditPart(view);

         case DbcEnumEditPart.VISUAL_ID:
            return new DbcEnumEditPart(view);

         case DbcEnumNameEditPart.VISUAL_ID:
            return new DbcEnumNameEditPart(view);

         case DbcProofEditPart.VISUAL_ID:
            return new DbcProofEditPart(view);

         case DbcProofObligationEditPart.VISUAL_ID:
            return new DbcProofObligationEditPart(view);

         case DbcPackage2EditPart.VISUAL_ID:
            return new DbcPackage2EditPart(view);

         case DbcPackageName2EditPart.VISUAL_ID:
            return new DbcPackageName2EditPart(view);

         case DbcClass2EditPart.VISUAL_ID:
            return new DbcClass2EditPart(view);

         case DbcClassName2EditPart.VISUAL_ID:
            return new DbcClassName2EditPart(view);

         case DbcInterface2EditPart.VISUAL_ID:
            return new DbcInterface2EditPart(view);

         case DbcInterfaceName2EditPart.VISUAL_ID:
            return new DbcInterfaceName2EditPart(view);

         case DbcEnum2EditPart.VISUAL_ID:
            return new DbcEnum2EditPart(view);

         case DbcEnumName2EditPart.VISUAL_ID:
            return new DbcEnumName2EditPart(view);

         case DbcProof2EditPart.VISUAL_ID:
            return new DbcProof2EditPart(view);

         case DbcProofObligation2EditPart.VISUAL_ID:
            return new DbcProofObligation2EditPart(view);

         case DbcInvariantEditPart.VISUAL_ID:
            return new DbcInvariantEditPart(view);

         case DbcInvariantNameEditPart.VISUAL_ID:
            return new DbcInvariantNameEditPart(view);

         case DbcInvariantTextEditPart.VISUAL_ID:
            return new DbcInvariantTextEditPart(view);

         case DbcAttributeEditPart.VISUAL_ID:
            return new DbcAttributeEditPart(view);

         case DbcAttributeNameTypeEditPart.VISUAL_ID:
            return new DbcAttributeNameTypeEditPart(view);

         case DbcMethodEditPart.VISUAL_ID:
            return new DbcMethodEditPart(view);

         case DbcMethodSignatureReturnTypeEditPart.VISUAL_ID:
            return new DbcMethodSignatureReturnTypeEditPart(view);

         case DbcOperationContractEditPart.VISUAL_ID:
            return new DbcOperationContractEditPart(view);

         case DbcOperationContractNameEditPart.VISUAL_ID:
            return new DbcOperationContractNameEditPart(view);

         case DbcOperationContractPreEditPart.VISUAL_ID:
            return new DbcOperationContractPreEditPart(view);

         case DbcOperationContractPostEditPart.VISUAL_ID:
            return new DbcOperationContractPostEditPart(view);

         case DbcConstructorEditPart.VISUAL_ID:
            return new DbcConstructorEditPart(view);

         case DbcConstructorSignatureEditPart.VISUAL_ID:
            return new DbcConstructorSignatureEditPart(view);

         case DbcEnumLiteralEditPart.VISUAL_ID:
            return new DbcEnumLiteralEditPart(view);

         case DbcEnumLiteralNameEditPart.VISUAL_ID:
            return new DbcEnumLiteralNameEditPart(view);

         case DbcAxiomEditPart.VISUAL_ID:
            return new DbcAxiomEditPart(view);

         case DbcAxiomNameEditPart.VISUAL_ID:
            return new DbcAxiomNameEditPart(view);

         case DbcAxiomDefinitionEditPart.VISUAL_ID:
            return new DbcAxiomDefinitionEditPart(view);

         case DbCAxiomContractEditPart.VISUAL_ID:
            return new DbCAxiomContractEditPart(view);

         case DbCAxiomContractNameEditPart.VISUAL_ID:
            return new DbCAxiomContractNameEditPart(view);

         case DbCAxiomContractPreEditPart.VISUAL_ID:
            return new DbCAxiomContractPreEditPart(view);

         case DbCAxiomContractDepEditPart.VISUAL_ID:
            return new DbCAxiomContractDepEditPart(view);

         case DbcPackageDbcPackageCompartmentEditPart.VISUAL_ID:
            return new DbcPackageDbcPackageCompartmentEditPart(view);

         case DbcPackageDbcPackageCompartment2EditPart.VISUAL_ID:
            return new DbcPackageDbcPackageCompartment2EditPart(view);

         case DbcClassDbcClassMainCompartmentEditPart.VISUAL_ID:
            return new DbcClassDbcClassMainCompartmentEditPart(view);

         case DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID:
            return new DbcClassDbcClassAttributeCompartmentEditPart(view);

         case DbcInterfaceDbcInterfaceMainCompartmentEditPart.VISUAL_ID:
            return new DbcInterfaceDbcInterfaceMainCompartmentEditPart(view);

         case DbcInterfaceDbcInterfaceAttributeCompartmentEditPart.VISUAL_ID:
            return new DbcInterfaceDbcInterfaceAttributeCompartmentEditPart(
                  view);

         case DbcEnumDbcEnumMainCompartmentEditPart.VISUAL_ID:
            return new DbcEnumDbcEnumMainCompartmentEditPart(view);

         case DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID:
            return new DbcEnumDbcEnumAttributeCompartmentEditPart(view);

         case DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID:
            return new DbcEnumDbcEnumLiteralCompartmentEditPart(view);

         case DbcMethodDbcMethodCompartmentEditPart.VISUAL_ID:
            return new DbcMethodDbcMethodCompartmentEditPart(view);

         case DbcConstructorDbcConstructorCompartmentEditPart.VISUAL_ID:
            return new DbcConstructorDbcConstructorCompartmentEditPart(view);

         case DbcAxiomDbcAxiomCompartmentEditPart.VISUAL_ID:
            return new DbcAxiomDbcAxiomCompartmentEditPart(view);

         case DbcInterfaceDbcInterfaceMainCompartment2EditPart.VISUAL_ID:
            return new DbcInterfaceDbcInterfaceMainCompartment2EditPart(view);

         case DbcInterfaceDbcInterfaceAttributeCompartment2EditPart.VISUAL_ID:
            return new DbcInterfaceDbcInterfaceAttributeCompartment2EditPart(
                  view);

         case DbcClassDbcClassMainCompartment2EditPart.VISUAL_ID:
            return new DbcClassDbcClassMainCompartment2EditPart(view);

         case DbcClassDbcClassAttributeCompartment2EditPart.VISUAL_ID:
            return new DbcClassDbcClassAttributeCompartment2EditPart(view);

         case DbcEnumDbcEnumMainCompartment2EditPart.VISUAL_ID:
            return new DbcEnumDbcEnumMainCompartment2EditPart(view);

         case DbcEnumDbcEnumAttributeCompartment2EditPart.VISUAL_ID:
            return new DbcEnumDbcEnumAttributeCompartment2EditPart(view);

         case DbcEnumDbcEnumLiteralCompartment2EditPart.VISUAL_ID:
            return new DbcEnumDbcEnumLiteralCompartment2EditPart(view);

         case DbcProofTargetEditPart.VISUAL_ID:
            return new DbcProofTargetEditPart(view);

         case DbcProofReferenceEditPart.VISUAL_ID:
            return new DbcProofReferenceEditPart(view);

         case DbcProofReferenceKindEditPart.VISUAL_ID:
            return new DbcProofReferenceKindEditPart(view);

         case DbcClassExtendsEditPart.VISUAL_ID:
            return new DbcClassExtendsEditPart(view);

         case DbcInterfaceExtendsEditPart.VISUAL_ID:
            return new DbcInterfaceExtendsEditPart(view);

         case AbstractDbcClassImplementsEditPart.VISUAL_ID:
            return new AbstractDbcClassImplementsEditPart(view);

         }
      }
      return createUnrecognizedEditPart(context, model);
   }

   /**
    * @generated
    */
   private EditPart createUnrecognizedEditPart(EditPart context, Object model) {
      // Handle creation of unrecognized child node EditParts here
      return null;
   }

   /**
    * @generated
    */
   public static CellEditorLocator getTextCellEditorLocator(
         ITextAwareEditPart source) {
      if (source.getFigure() instanceof WrappingLabel)
         return new TextCellEditorLocator((WrappingLabel) source.getFigure());
      else {
         return new LabelCellEditorLocator((Label) source.getFigure());
      }
   }

   /**
    * @generated
    */
   static private class TextCellEditorLocator implements CellEditorLocator {

      /**
       * @generated
       */
      private WrappingLabel wrapLabel;

      /**
       * @generated
       */
      public TextCellEditorLocator(WrappingLabel wrapLabel) {
         this.wrapLabel = wrapLabel;
      }

      /**
       * @generated
       */
      public WrappingLabel getWrapLabel() {
         return wrapLabel;
      }

      /**
       * @generated
       */
      public void relocate(CellEditor celleditor) {
         Text text = (Text) celleditor.getControl();
         Rectangle rect = getWrapLabel().getTextBounds().getCopy();
         getWrapLabel().translateToAbsolute(rect);
         if (!text.getFont().isDisposed()) {
            if (getWrapLabel().isTextWrapOn()
                  && getWrapLabel().getText().length() > 0) {
               rect.setSize(new Dimension(text.computeSize(rect.width,
                     SWT.DEFAULT)));
            }
            else {
               int avr = FigureUtilities.getFontMetrics(text.getFont())
                     .getAverageCharWidth();
               rect.setSize(new Dimension(text.computeSize(SWT.DEFAULT,
                     SWT.DEFAULT)).expand(avr * 2, 0));
            }
         }
         if (!rect.equals(new Rectangle(text.getBounds()))) {
            text.setBounds(rect.x, rect.y, rect.width, rect.height);
         }
      }
   }

   /**
    * @generated
    */
   private static class LabelCellEditorLocator implements CellEditorLocator {

      /**
       * @generated
       */
      private Label label;

      /**
       * @generated
       */
      public LabelCellEditorLocator(Label label) {
         this.label = label;
      }

      /**
       * @generated
       */
      public Label getLabel() {
         return label;
      }

      /**
       * @generated
       */
      public void relocate(CellEditor celleditor) {
         Text text = (Text) celleditor.getControl();
         Rectangle rect = getLabel().getTextBounds().getCopy();
         getLabel().translateToAbsolute(rect);
         if (!text.getFont().isDisposed()) {
            int avr = FigureUtilities.getFontMetrics(text.getFont())
                  .getAverageCharWidth();
            rect.setSize(new Dimension(text.computeSize(SWT.DEFAULT,
                  SWT.DEFAULT)).expand(avr * 2, 0));
         }
         if (!rect.equals(new Rectangle(text.getBounds()))) {
            text.setBounds(rect.x, rect.y, rect.width, rect.height);
         }
      }
   }
}