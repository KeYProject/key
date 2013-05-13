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

import org.eclipse.draw2d.GridData;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.geometry.Dimension;
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
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcPackageItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbcPackageEditPart extends ShapeNodeEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 2007;

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
   public DbcPackageEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcPackageItemSemanticEditPolicy());
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
      return primaryShape = new DbcPackageFigure();
   }

   /**
    * @generated
    */
   public DbcPackageFigure getPrimaryShape() {
      return (DbcPackageFigure) primaryShape;
   }

   /**
    * @generated
    */
   protected boolean addFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcPackageNameEditPart) {
         ((DbcPackageNameEditPart) childEditPart).setLabel(getPrimaryShape()
               .getFigureDbcPackageNameFigure());
         return true;
      }
      if (childEditPart instanceof DbcPackageDbcPackageCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcPackageCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.add(((DbcPackageDbcPackageCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean removeFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcPackageNameEditPart) {
         return true;
      }
      if (childEditPart instanceof DbcPackageDbcPackageCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcPackageCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.remove(((DbcPackageDbcPackageCompartmentEditPart) childEditPart)
               .getFigure());
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
      if (editPart instanceof DbcPackageDbcPackageCompartmentEditPart) {
         return getPrimaryShape().getFigureDbcPackageCompartmentRectangle();
      }
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
            .getType(DbcPackageNameEditPart.VISUAL_ID));
   }

   /**
    * @generated
    */
   public class DbcPackageFigure extends RectangleFigure {

      /**
       * @generated
       */
      private WrappingLabel fFigureDbcPackageNameFigure;
      /**
       * @generated
       */
      private RectangleFigure fFigureDbcPackageCompartmentRectangle;

      /**
       * @generated
       */
      public DbcPackageFigure() {

         GridLayout layoutThis = new GridLayout();
         layoutThis.numColumns = 1;
         layoutThis.makeColumnsEqualWidth = true;
         layoutThis.horizontalSpacing = -1;
         layoutThis.verticalSpacing = -2;
         layoutThis.marginWidth = 0;
         layoutThis.marginHeight = 0;
         this.setLayoutManager(layoutThis);

         this.setFill(false);
         this.setOutline(false);
         this.setMinimumSize(new Dimension(getMapMode().DPtoLP(50),
               getMapMode().DPtoLP(50)));
         createContents();
      }

      /**
       * @generated
       */
      private void createContents() {

         RectangleFigure dbcPackageNameRectangle0 = new RectangleFigure();
         dbcPackageNameRectangle0.setFill(false);
         dbcPackageNameRectangle0.setOutline(false);

         GridData constraintDbcPackageNameRectangle0 = new GridData();
         constraintDbcPackageNameRectangle0.verticalAlignment = GridData.CENTER;
         constraintDbcPackageNameRectangle0.horizontalAlignment = GridData.FILL;
         constraintDbcPackageNameRectangle0.horizontalIndent = 0;
         constraintDbcPackageNameRectangle0.horizontalSpan = 1;
         constraintDbcPackageNameRectangle0.verticalSpan = 1;
         constraintDbcPackageNameRectangle0.grabExcessHorizontalSpace = true;
         constraintDbcPackageNameRectangle0.grabExcessVerticalSpace = false;
         this.add(dbcPackageNameRectangle0, constraintDbcPackageNameRectangle0);

         GridLayout layoutDbcPackageNameRectangle0 = new GridLayout();
         layoutDbcPackageNameRectangle0.numColumns = 2;
         layoutDbcPackageNameRectangle0.makeColumnsEqualWidth = true;
         layoutDbcPackageNameRectangle0.horizontalSpacing = 0;
         layoutDbcPackageNameRectangle0.verticalSpacing = 0;
         layoutDbcPackageNameRectangle0.marginWidth = 0;
         layoutDbcPackageNameRectangle0.marginHeight = 0;
         dbcPackageNameRectangle0
               .setLayoutManager(layoutDbcPackageNameRectangle0);

         RectangleFigure dbcPackageNameLeftRectangle1 = new RectangleFigure();

         GridData constraintDbcPackageNameLeftRectangle1 = new GridData();
         constraintDbcPackageNameLeftRectangle1.verticalAlignment = GridData.CENTER;
         constraintDbcPackageNameLeftRectangle1.horizontalAlignment = GridData.FILL;
         constraintDbcPackageNameLeftRectangle1.horizontalIndent = 0;
         constraintDbcPackageNameLeftRectangle1.horizontalSpan = 1;
         constraintDbcPackageNameLeftRectangle1.verticalSpan = 1;
         constraintDbcPackageNameLeftRectangle1.grabExcessHorizontalSpace = true;
         constraintDbcPackageNameLeftRectangle1.grabExcessVerticalSpace = false;
         dbcPackageNameRectangle0.add(dbcPackageNameLeftRectangle1,
               constraintDbcPackageNameLeftRectangle1);

         GridLayout layoutDbcPackageNameLeftRectangle1 = new GridLayout();
         layoutDbcPackageNameLeftRectangle1.numColumns = 1;
         layoutDbcPackageNameLeftRectangle1.makeColumnsEqualWidth = true;
         layoutDbcPackageNameLeftRectangle1.horizontalSpacing = 0;
         layoutDbcPackageNameLeftRectangle1.verticalSpacing = 0;
         layoutDbcPackageNameLeftRectangle1.marginWidth = 3;
         layoutDbcPackageNameLeftRectangle1.marginHeight = 5;
         dbcPackageNameLeftRectangle1
               .setLayoutManager(layoutDbcPackageNameLeftRectangle1);

         fFigureDbcPackageNameFigure = new WrappingLabel();
         fFigureDbcPackageNameFigure.setText("<...>");
         fFigureDbcPackageNameFigure.setMinimumSize(new Dimension(getMapMode()
               .DPtoLP(1), getMapMode().DPtoLP(1)));

         GridData constraintFFigureDbcPackageNameFigure = new GridData();
         constraintFFigureDbcPackageNameFigure.verticalAlignment = GridData.CENTER;
         constraintFFigureDbcPackageNameFigure.horizontalAlignment = GridData.BEGINNING;
         constraintFFigureDbcPackageNameFigure.horizontalIndent = 0;
         constraintFFigureDbcPackageNameFigure.horizontalSpan = 1;
         constraintFFigureDbcPackageNameFigure.verticalSpan = 1;
         constraintFFigureDbcPackageNameFigure.grabExcessHorizontalSpace = true;
         constraintFFigureDbcPackageNameFigure.grabExcessVerticalSpace = false;
         dbcPackageNameLeftRectangle1.add(fFigureDbcPackageNameFigure,
               constraintFFigureDbcPackageNameFigure);

         RectangleFigure dbcPackageNameRightRectangle1 = new RectangleFigure();
         dbcPackageNameRightRectangle1.setFill(false);
         dbcPackageNameRightRectangle1.setOutline(false);

         GridData constraintDbcPackageNameRightRectangle1 = new GridData();
         constraintDbcPackageNameRightRectangle1.verticalAlignment = GridData.CENTER;
         constraintDbcPackageNameRightRectangle1.horizontalAlignment = GridData.FILL;
         constraintDbcPackageNameRightRectangle1.horizontalIndent = 0;
         constraintDbcPackageNameRightRectangle1.horizontalSpan = 1;
         constraintDbcPackageNameRightRectangle1.verticalSpan = 1;
         constraintDbcPackageNameRightRectangle1.grabExcessHorizontalSpace = true;
         constraintDbcPackageNameRightRectangle1.grabExcessVerticalSpace = false;
         dbcPackageNameRectangle0.add(dbcPackageNameRightRectangle1,
               constraintDbcPackageNameRightRectangle1);

         fFigureDbcPackageCompartmentRectangle = new RectangleFigure();
         fFigureDbcPackageCompartmentRectangle.setBorder(new MarginBorder(
               getMapMode().DPtoLP(0), getMapMode().DPtoLP(5), getMapMode()
                     .DPtoLP(5), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcPackageCompartmentRectangle = new GridData();
         constraintFFigureDbcPackageCompartmentRectangle.verticalAlignment = GridData.FILL;
         constraintFFigureDbcPackageCompartmentRectangle.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcPackageCompartmentRectangle.horizontalIndent = 0;
         constraintFFigureDbcPackageCompartmentRectangle.horizontalSpan = 1;
         constraintFFigureDbcPackageCompartmentRectangle.verticalSpan = 1;
         constraintFFigureDbcPackageCompartmentRectangle.grabExcessHorizontalSpace = true;
         constraintFFigureDbcPackageCompartmentRectangle.grabExcessVerticalSpace = true;
         this.add(fFigureDbcPackageCompartmentRectangle,
               constraintFFigureDbcPackageCompartmentRectangle);

      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcPackageNameFigure() {
         return fFigureDbcPackageNameFigure;
      }

      /**
       * @generated
       */
      public RectangleFigure getFigureDbcPackageCompartmentRectangle() {
         return fFigureDbcPackageCompartmentRectangle;
      }

   }

}