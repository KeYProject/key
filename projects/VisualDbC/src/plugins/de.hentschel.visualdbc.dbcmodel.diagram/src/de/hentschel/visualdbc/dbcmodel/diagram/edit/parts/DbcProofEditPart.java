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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.parts;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.GridData;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.ScalablePolygonShape;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcProofItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcProofEditPart extends ShapeNodeEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 2014;

   /**
    * @generated
    */
   protected IFigure contentPane;

   /**
    * @generated
    */
   protected IFigure primaryShape;

   /**
    * @generated
    */
   public DbcProofEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcProofItemSemanticEditPolicy());
      installEditPolicy(EditPolicy.LAYOUT_ROLE, createLayoutEditPolicy());
      // XXX need an SCR to runtime to have another abstract superclass that would let children add reasonable editpolicies
      // removeEditPolicy(org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles.CONNECTION_HANDLES_ROLE);
   }

   /**
    * @generated
    */
   protected LayoutEditPolicy createLayoutEditPolicy() {
      org.eclipse.gmf.runtime.diagram.ui.editpolicies.LayoutEditPolicy lep = new org.eclipse.gmf.runtime.diagram.ui.editpolicies.LayoutEditPolicy() {

         protected EditPolicy createChildEditPolicy(EditPart child) {
            EditPolicy result = child
                  .getEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE);
            if (result == null) {
               result = new NonResizableEditPolicy();
            }
            return result;
         }

         protected Command getMoveChildrenCommand(Request request) {
            return null;
         }

         protected Command getCreateCommand(CreateRequest request) {
            return null;
         }
      };
      return lep;
   }

   /**
    * @generated
    */
   protected IFigure createNodeShape() {
      return primaryShape = new DbcProofFigure();
   }

   /**
    * @generated
    */
   public DbcProofFigure getPrimaryShape() {
      return (DbcProofFigure) primaryShape;
   }

   /**
    * @generated
    */
   protected boolean addFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcProofObligationEditPart) {
         ((DbcProofObligationEditPart) childEditPart)
               .setLabel(getPrimaryShape().getFigureDbcProofNameFigure());
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean removeFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcProofObligationEditPart) {
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected void addChildVisual(EditPart childEditPart, int index) {
      if (addFixedChild(childEditPart)) {
         return;
      }
      super.addChildVisual(childEditPart, -1);
   }

   /**
    * @generated
    */
   protected void removeChildVisual(EditPart childEditPart) {
      if (removeFixedChild(childEditPart)) {
         return;
      }
      super.removeChildVisual(childEditPart);
   }

   /**
    * @generated
    */
   protected IFigure getContentPaneFor(IGraphicalEditPart editPart) {
      return getContentPane();
   }

   /**
    * @generated
    */
   protected NodeFigure createNodePlate() {
      DefaultSizeNodeFigure result = new DefaultSizeNodeFigure(40, 40);
      return result;
   }

   /**
    * Creates figure for this edit part.
    * 
    * Body of this method does not depend on settings in generation model
    * so you may safely remove <i>generated</i> tag and modify it.
    * 
    * @generated
    */
   protected NodeFigure createNodeFigure() {
      NodeFigure figure = createNodePlate();
      figure.setLayoutManager(new StackLayout());
      IFigure shape = createNodeShape();
      figure.add(shape);
      contentPane = setupContentPane(shape);
      return figure;
   }

   /**
    * Default implementation treats passed figure as content pane.
    * Respects layout one may have set for generated figure.
    * @param nodeShape instance of generated figure class
    * @generated
    */
   protected IFigure setupContentPane(IFigure nodeShape) {
      if (nodeShape.getLayoutManager() == null) {
         ConstrainedToolbarLayout layout = new ConstrainedToolbarLayout();
         layout.setSpacing(5);
         nodeShape.setLayoutManager(layout);
      }
      return nodeShape; // use nodeShape itself as contentPane
   }

   /**
    * @generated
    */
   public IFigure getContentPane() {
      if (contentPane != null) {
         return contentPane;
      }
      return super.getContentPane();
   }

   /**
    * @generated
    */
   protected void setForegroundColor(Color color) {
      if (primaryShape != null) {
         primaryShape.setForegroundColor(color);
      }
   }

   /**
    * @generated
    */
   protected void setBackgroundColor(Color color) {
      if (primaryShape != null) {
         primaryShape.setBackgroundColor(color);
      }
   }

   /**
    * @generated
    */
   protected void setLineWidth(int width) {
      if (primaryShape instanceof Shape) {
         ((Shape) primaryShape).setLineWidth(width);
      }
   }

   /**
    * @generated
    */
   protected void setLineType(int style) {
      if (primaryShape instanceof Shape) {
         ((Shape) primaryShape).setLineStyle(style);
      }
   }

   /**
    * @generated
    */
   public EditPart getPrimaryChildEditPart() {
      return getChildBySemanticHint(DbCVisualIDRegistry
            .getType(DbcProofObligationEditPart.VISUAL_ID));
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnSource() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcProofTarget_4001);
      types.add(DbCElementTypes.DbcProofReference_4002);
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnSourceAndTarget(
         IGraphicalEditPart targetEditPart) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
      if (targetEditPart instanceof DbcInterfaceEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcClassEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcEnumEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcClass2EditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcInterface2EditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcEnum2EditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcMethodEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcOperationContractEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcConstructorEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbCAxiomContractEditPart) {
         types.add(DbCElementTypes.DbcProofTarget_4001);
      }
      if (targetEditPart instanceof DbcInterfaceEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcClassEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcEnumEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcClass2EditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcInterface2EditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcEnum2EditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcInvariantEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcAttributeEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcMethodEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcOperationContractEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcConstructorEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcEnumLiteralEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbcAxiomEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      if (targetEditPart instanceof DbCAxiomContractEditPart) {
         types.add(DbCElementTypes.DbcProofReference_4002);
      }
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMATypesForTarget(IElementType relationshipType) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
      if (relationshipType == DbCElementTypes.DbcProofTarget_4001) {
         types.add(DbCElementTypes.DbcInterface_2011);
         types.add(DbCElementTypes.DbcClass_2012);
         types.add(DbCElementTypes.DbcEnum_2013);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcOperationContract_3026);
         types.add(DbCElementTypes.DbcConstructor_3010);
         types.add(DbCElementTypes.DbCAxiomContract_3037);
      }
      else if (relationshipType == DbCElementTypes.DbcProofReference_4002) {
         types.add(DbCElementTypes.DbcInterface_2011);
         types.add(DbCElementTypes.DbcClass_2012);
         types.add(DbCElementTypes.DbcEnum_2013);
         types.add(DbCElementTypes.DbcClass_3031);
         types.add(DbCElementTypes.DbcInterface_3032);
         types.add(DbCElementTypes.DbcEnum_3033);
         types.add(DbCElementTypes.DbcInvariant_3035);
         types.add(DbCElementTypes.DbcAttribute_3011);
         types.add(DbCElementTypes.DbcMethod_3009);
         types.add(DbCElementTypes.DbcOperationContract_3026);
         types.add(DbCElementTypes.DbcConstructor_3010);
         types.add(DbCElementTypes.DbcEnumLiteral_3020);
         types.add(DbCElementTypes.DbcAxiom_3036);
         types.add(DbCElementTypes.DbCAxiomContract_3037);
      }
      return types;
   }

   /**
    * @generated
    */
   public class DbcProofFigure extends ScalablePolygonShape {

      /**
       * @generated
       */
      private WrappingLabel fFigureDbcProofNameFigure;

      /**
       * @generated
       */
      public DbcProofFigure() {

         GridLayout layoutThis = new GridLayout();
         layoutThis.numColumns = 1;
         layoutThis.makeColumnsEqualWidth = true;
         layoutThis.horizontalSpacing = 0;
         layoutThis.verticalSpacing = 0;
         layoutThis.marginWidth = 10;
         layoutThis.marginHeight = 5;
         this.setLayoutManager(layoutThis);

         this.addPoint(new Point(getMapMode().DPtoLP(0), getMapMode()
               .DPtoLP(20)));
         this.addPoint(new Point(getMapMode().DPtoLP(10), getMapMode()
               .DPtoLP(0)));
         this.addPoint(new Point(getMapMode().DPtoLP(90), getMapMode()
               .DPtoLP(0)));
         this.addPoint(new Point(getMapMode().DPtoLP(100), getMapMode().DPtoLP(
               20)));
         this.addPoint(new Point(getMapMode().DPtoLP(90), getMapMode().DPtoLP(
               40)));
         this.addPoint(new Point(getMapMode().DPtoLP(10), getMapMode().DPtoLP(
               40)));
         this.setFill(true);
         this.setBackgroundColor(THIS_BACK);
         createContents();
      }

      /**
       * @generated
       */
      private void createContents() {

         fFigureDbcProofNameFigure = new WrappingLabel();
         fFigureDbcProofNameFigure.setText("<...>");

         GridData constraintFFigureDbcProofNameFigure = new GridData();
         constraintFFigureDbcProofNameFigure.verticalAlignment = GridData.CENTER;
         constraintFFigureDbcProofNameFigure.horizontalAlignment = GridData.CENTER;
         constraintFFigureDbcProofNameFigure.horizontalIndent = 0;
         constraintFFigureDbcProofNameFigure.horizontalSpan = 1;
         constraintFFigureDbcProofNameFigure.verticalSpan = 1;
         constraintFFigureDbcProofNameFigure.grabExcessHorizontalSpace = true;
         constraintFFigureDbcProofNameFigure.grabExcessVerticalSpace = true;
         this.add(fFigureDbcProofNameFigure,
               constraintFFigureDbcProofNameFigure);

      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcProofNameFigure() {
         return fFigureDbcProofNameFigure;
      }

   }

   /**
    * @generated
    */
   static final Color THIS_BACK = new Color(null, 204, 204, 250);

}