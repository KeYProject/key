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
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.RoundedRectangle;
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
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCAxiomContractItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbCAxiomContractEditPart extends ShapeNodeEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 3037;

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
   public DbCAxiomContractEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbCAxiomContractItemSemanticEditPolicy());
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
      return primaryShape = new DbcAxiomContractFigure();
   }

   /**
    * @generated
    */
   public DbcAxiomContractFigure getPrimaryShape() {
      return (DbcAxiomContractFigure) primaryShape;
   }

   /**
    * @generated
    */
   protected boolean addFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbCAxiomContractNameEditPart) {
         ((DbCAxiomContractNameEditPart) childEditPart)
               .setLabel(getPrimaryShape()
                     .getFigureDbcAxiomContractNameFigure());
         return true;
      }
      if (childEditPart instanceof DbCAxiomContractPreEditPart) {
         ((DbCAxiomContractPreEditPart) childEditPart)
               .setLabel(getPrimaryShape().getFigureDbcAxiomContractPreFigure());
         return true;
      }
      if (childEditPart instanceof DbCAxiomContractDepEditPart) {
         ((DbCAxiomContractDepEditPart) childEditPart)
               .setLabel(getPrimaryShape().getFigureDbcAxiomContractDepFigure());
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean removeFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbCAxiomContractNameEditPart) {
         return true;
      }
      if (childEditPart instanceof DbCAxiomContractPreEditPart) {
         return true;
      }
      if (childEditPart instanceof DbCAxiomContractDepEditPart) {
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
            .getType(DbCAxiomContractNameEditPart.VISUAL_ID));
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnTarget() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcProofTarget_4001);
      types.add(DbCElementTypes.DbcProofReference_4002);
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMATypesForSource(IElementType relationshipType) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
      if (relationshipType == DbCElementTypes.DbcProofTarget_4001) {
         types.add(DbCElementTypes.DbcProof_2014);
         types.add(DbCElementTypes.DbcProof_3034);
      }
      else if (relationshipType == DbCElementTypes.DbcProofReference_4002) {
         types.add(DbCElementTypes.DbcProof_2014);
         types.add(DbCElementTypes.DbcProof_3034);
      }
      return types;
   }

   /**
    * @generated
    */
   public class DbcAxiomContractFigure extends RoundedRectangle {
      /**
       * @generated NOT
       */
      private Color originalForegroundColor;

      /**
       * @generated NOT
       */
      private int originalLineWidth;

      /**
       * @generated
       */
      private WrappingLabel fFigureDbcAxiomContractNameFigure;
      /**
       * @generated
       */
      private WrappingLabel fFigureDbcAxiomContractPreFigure;
      /**
       * @generated
       */
      private WrappingLabel fFigureDbcAxiomContractDepFigure;

      /**
       * @generated
       */
      public DbcAxiomContractFigure() {

         GridLayout layoutThis = new GridLayout();
         layoutThis.numColumns = 1;
         layoutThis.makeColumnsEqualWidth = true;
         layoutThis.horizontalSpacing = 0;
         layoutThis.verticalSpacing = -1;
         layoutThis.marginWidth = 0;
         layoutThis.marginHeight = 0;
         this.setLayoutManager(layoutThis);

         this.setCornerDimensions(new Dimension(getMapMode().DPtoLP(45),
               getMapMode().DPtoLP(45)));
         this.setBackgroundColor(THIS_BACK);
         createContents();
      }

      /**
       * @generated NOT
       */
      private void createContents() {

         fFigureDbcAxiomContractNameFigure = new WrappingLabel();
         fFigureDbcAxiomContractNameFigure.setText("<...>");
         fFigureDbcAxiomContractNameFigure.setBorder(new MarginBorder(
               getMapMode().DPtoLP(5), getMapMode().DPtoLP(15), getMapMode()
                     .DPtoLP(3), getMapMode().DPtoLP(15)));

         GridData constraintFFigureDbcAxiomContractNameFigure = new GridData();
         constraintFFigureDbcAxiomContractNameFigure.verticalAlignment = GridData.CENTER;
         constraintFFigureDbcAxiomContractNameFigure.horizontalAlignment = GridData.CENTER;
         constraintFFigureDbcAxiomContractNameFigure.horizontalIndent = 0;
         constraintFFigureDbcAxiomContractNameFigure.horizontalSpan = 1;
         constraintFFigureDbcAxiomContractNameFigure.verticalSpan = 1;
         constraintFFigureDbcAxiomContractNameFigure.grabExcessHorizontalSpace = true;
         constraintFFigureDbcAxiomContractNameFigure.grabExcessVerticalSpace = false;
         this.add(fFigureDbcAxiomContractNameFigure,
               constraintFFigureDbcAxiomContractNameFigure);

         RectangleFigure dbcAxiomContractPreBorder0 = new RectangleFigure();

         GridData constraintDbcAxiomContractPreBorder0 = new GridData();
         constraintDbcAxiomContractPreBorder0.verticalAlignment = GridData.FILL;
         constraintDbcAxiomContractPreBorder0.horizontalAlignment = GridData.FILL;
         constraintDbcAxiomContractPreBorder0.horizontalIndent = 0;
         constraintDbcAxiomContractPreBorder0.horizontalSpan = 1;
         constraintDbcAxiomContractPreBorder0.verticalSpan = 1;
         constraintDbcAxiomContractPreBorder0.grabExcessHorizontalSpace = true;
         constraintDbcAxiomContractPreBorder0.grabExcessVerticalSpace = true;
         this.add(dbcAxiomContractPreBorder0,
               constraintDbcAxiomContractPreBorder0);

         GridLayout layoutDbcAxiomContractPreBorder0 = new GridLayout();
         layoutDbcAxiomContractPreBorder0.numColumns = 1;
         layoutDbcAxiomContractPreBorder0.makeColumnsEqualWidth = true;
         dbcAxiomContractPreBorder0
               .setLayoutManager(layoutDbcAxiomContractPreBorder0);

         fFigureDbcAxiomContractPreFigure = new WrappingLabel();
         fFigureDbcAxiomContractPreFigure.setText("<...>");
         fFigureDbcAxiomContractPreFigure.setTextWrap(true);

         GridData constraintFFigureDbcAxiomContractPreFigure = new GridData();
         constraintFFigureDbcAxiomContractPreFigure.verticalAlignment = GridData.FILL;
         constraintFFigureDbcAxiomContractPreFigure.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcAxiomContractPreFigure.horizontalIndent = 0;
         constraintFFigureDbcAxiomContractPreFigure.horizontalSpan = 1;
         constraintFFigureDbcAxiomContractPreFigure.verticalSpan = 1;
         constraintFFigureDbcAxiomContractPreFigure.grabExcessHorizontalSpace = true;
         constraintFFigureDbcAxiomContractPreFigure.grabExcessVerticalSpace = true;
         dbcAxiomContractPreBorder0.add(fFigureDbcAxiomContractPreFigure,
               constraintFFigureDbcAxiomContractPreFigure);

         RectangleFigure dbcAxiomContractDepBorder0 = new RectangleFigure();

         GridData constraintDbcAxiomContractDepBorder0 = new GridData();
         constraintDbcAxiomContractDepBorder0.verticalAlignment = GridData.FILL;
         constraintDbcAxiomContractDepBorder0.horizontalAlignment = GridData.FILL;
         constraintDbcAxiomContractDepBorder0.horizontalIndent = 0;
         constraintDbcAxiomContractDepBorder0.horizontalSpan = 1;
         constraintDbcAxiomContractDepBorder0.verticalSpan = 1;
         constraintDbcAxiomContractDepBorder0.grabExcessHorizontalSpace = true;
         constraintDbcAxiomContractDepBorder0.grabExcessVerticalSpace = true;
         this.add(dbcAxiomContractDepBorder0,
               constraintDbcAxiomContractDepBorder0);

         GridLayout layoutDbcAxiomContractDepBorder0 = new GridLayout();
         layoutDbcAxiomContractDepBorder0.numColumns = 1;
         layoutDbcAxiomContractDepBorder0.makeColumnsEqualWidth = true;
         dbcAxiomContractDepBorder0
               .setLayoutManager(layoutDbcAxiomContractDepBorder0);

         fFigureDbcAxiomContractDepFigure = new WrappingLabel();
         fFigureDbcAxiomContractDepFigure.setText("<...>");
         fFigureDbcAxiomContractDepFigure.setTextWrap(true);

         GridData constraintFFigureDbcAxiomContractDepFigure = new GridData();
         constraintFFigureDbcAxiomContractDepFigure.verticalAlignment = GridData.FILL;
         constraintFFigureDbcAxiomContractDepFigure.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcAxiomContractDepFigure.horizontalIndent = 0;
         constraintFFigureDbcAxiomContractDepFigure.horizontalSpan = 1;
         constraintFFigureDbcAxiomContractDepFigure.verticalSpan = 1;
         constraintFFigureDbcAxiomContractDepFigure.grabExcessHorizontalSpace = true;
         constraintFFigureDbcAxiomContractDepFigure.grabExcessVerticalSpace = true;
         dbcAxiomContractDepBorder0.add(fFigureDbcAxiomContractDepFigure,
               constraintFFigureDbcAxiomContractDepFigure);

      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcAxiomContractNameFigure() {
         return fFigureDbcAxiomContractNameFigure;
      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcAxiomContractPreFigure() {
         return fFigureDbcAxiomContractPreFigure;
      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcAxiomContractDepFigure() {
         return fFigureDbcAxiomContractDepFigure;
      }

      /**
       * @generated NOT
       */
      public void highlight(Color highlightForegroundColor, int lineWidth) {
         if (originalForegroundColor == null) {
            this.originalForegroundColor = getForegroundColor();
            this.originalLineWidth = getLineWidth();
         }
         super.setForegroundColor(highlightForegroundColor);
         super.setLineWidth(lineWidth);
         for (Object child :getChildren()) {
            if (child instanceof Shape) {
               ((Shape)child).setLineWidth(lineWidth);
            }
         }
      }
      
      /**
       * @generated NOT
       */
      public void disableHighlighting() {
         if (originalForegroundColor != null) {
            super.setForegroundColor(originalForegroundColor);
            super.setLineWidth(originalLineWidth);
            for (Object child :getChildren()) {
               if (child instanceof Shape) {
                  ((Shape)child).setLineWidth(originalLineWidth);
               }
            }
            originalForegroundColor = null;
         }
      }

      /**
       * @generated NOT
       */
      @Override
      public void setForegroundColor(Color fg) {
         if (originalForegroundColor == null) {
            super.setForegroundColor(fg);
         }
         else {
            originalForegroundColor = fg;
         }
      }

      /**
       * @generated NOT
       */
      @Override
      public void setLineWidth(int w) {
         if (originalForegroundColor == null) {
            super.setLineWidth(w);
         }
         else {
            originalLineWidth = w;
         }
      }

   }

   /**
    * @generated
    */
   static final Color THIS_BACK = new Color(null, 240, 240, 250);

}