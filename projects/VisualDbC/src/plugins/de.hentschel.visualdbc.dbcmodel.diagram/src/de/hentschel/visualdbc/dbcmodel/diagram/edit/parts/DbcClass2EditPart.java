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

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.GridData;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gmf.runtime.diagram.core.edithelpers.CreateElementRequestAdapter;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.CreationEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateViewAndElementRequest;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcClass2ItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcClass2EditPart extends ShapeNodeEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 3031;

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
   public DbcClass2EditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      installEditPolicy(EditPolicyRoles.CREATION_ROLE, new CreationEditPolicy());
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcClass2ItemSemanticEditPolicy());
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
      return primaryShape = new DbcClassFigure();
   }

   /**
    * @generated
    */
   public DbcClassFigure getPrimaryShape() {
      return (DbcClassFigure) primaryShape;
   }

   /**
    * @generated
    */
   protected boolean addFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcClassName2EditPart) {
         ((DbcClassName2EditPart) childEditPart).setLabel(getPrimaryShape()
               .getFigureDbcClassNameFigure());
         return true;
      }
      if (childEditPart instanceof DbcClassDbcClassMainCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcClassMainCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.add(((DbcClassDbcClassMainCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      if (childEditPart instanceof DbcClassDbcClassAttributeCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcClassAttributeCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.add(((DbcClassDbcClassAttributeCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean removeFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcClassName2EditPart) {
         return true;
      }
      if (childEditPart instanceof DbcClassDbcClassMainCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcClassMainCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.remove(((DbcClassDbcClassMainCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      if (childEditPart instanceof DbcClassDbcClassAttributeCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcClassAttributeCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.remove(((DbcClassDbcClassAttributeCompartmentEditPart) childEditPart)
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
      if (editPart instanceof DbcClassDbcClassMainCompartmentEditPart) {
         return getPrimaryShape().getFigureDbcClassMainCompartmentRectangle();
      }
      if (editPart instanceof DbcClassDbcClassAttributeCompartmentEditPart) {
         return getPrimaryShape()
               .getFigureDbcClassAttributeCompartmentRectangle();
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
            .getType(DbcClassName2EditPart.VISUAL_ID));
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnSource() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(2);
      types.add(DbCElementTypes.DbcClassExtends_4003);
      types.add(DbCElementTypes.AbstractDbcClassImplements_4005);
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnSourceAndTarget(
         IGraphicalEditPart targetEditPart) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
      if (targetEditPart instanceof DbcClassEditPart) {
         types.add(DbCElementTypes.DbcClassExtends_4003);
      }
      if (targetEditPart instanceof de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart) {
         types.add(DbCElementTypes.DbcClassExtends_4003);
      }
      if (targetEditPart instanceof DbcInterfaceEditPart) {
         types.add(DbCElementTypes.AbstractDbcClassImplements_4005);
      }
      if (targetEditPart instanceof DbcInterface2EditPart) {
         types.add(DbCElementTypes.AbstractDbcClassImplements_4005);
      }
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMATypesForTarget(IElementType relationshipType) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
      if (relationshipType == DbCElementTypes.DbcClassExtends_4003) {
         types.add(DbCElementTypes.DbcClass_2012);
         types.add(DbCElementTypes.DbcClass_3031);
      }
      else if (relationshipType == DbCElementTypes.AbstractDbcClassImplements_4005) {
         types.add(DbCElementTypes.DbcInterface_2011);
         types.add(DbCElementTypes.DbcInterface_3032);
      }
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnTarget() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(3);
      types.add(DbCElementTypes.DbcProofTarget_4001);
      types.add(DbCElementTypes.DbcProofReference_4002);
      types.add(DbCElementTypes.DbcClassExtends_4003);
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
      else if (relationshipType == DbCElementTypes.DbcClassExtends_4003) {
         types.add(DbCElementTypes.DbcClass_2012);
         types.add(DbCElementTypes.DbcClass_3031);
      }
      return types;
   }

   /**
    * @generated
    */
   public EditPart getTargetEditPart(Request request) {
      if (request instanceof CreateViewAndElementRequest) {
         CreateElementRequestAdapter adapter = ((CreateViewAndElementRequest) request)
               .getViewAndElementDescriptor().getCreateElementRequestAdapter();
         IElementType type = (IElementType) adapter
               .getAdapter(IElementType.class);
         if (type == DbCElementTypes.DbcAttribute_3011) {
            return getChildBySemanticHint(DbCVisualIDRegistry
                  .getType(DbcClassDbcClassAttributeCompartmentEditPart.VISUAL_ID));
         }
      }
      return super.getTargetEditPart(request);
   }

   /**
    * @generated
    */
   public class DbcClassFigure extends RectangleFigure {
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
      private WrappingLabel fFigureDbcClassNameFigure;
      /**
       * @generated
       */
      private RectangleFigure fFigureDbcClassAttributeCompartmentRectangle;
      /**
       * @generated
       */
      private RectangleFigure fFigureDbcClassMainCompartmentRectangle;

      /**
       * @generated
       */
      public DbcClassFigure() {

         GridLayout layoutThis = new GridLayout();
         layoutThis.numColumns = 1;
         layoutThis.makeColumnsEqualWidth = false;
         layoutThis.horizontalSpacing = 0;
         layoutThis.verticalSpacing = 0;
         layoutThis.marginWidth = 0;
         layoutThis.marginHeight = 0;
         this.setLayoutManager(layoutThis);

         this.setBackgroundColor(THIS_BACK);
         createContents();
      }

      /**
       * @generated
       */
      private void createContents() {

         fFigureDbcClassNameFigure = new WrappingLabel();
         fFigureDbcClassNameFigure.setText("<...>");
         fFigureDbcClassNameFigure.setBorder(new MarginBorder(getMapMode()
               .DPtoLP(5), getMapMode().DPtoLP(5), getMapMode().DPtoLP(3),
               getMapMode().DPtoLP(5)));

         this.add(fFigureDbcClassNameFigure);

         fFigureDbcClassAttributeCompartmentRectangle = new RectangleFigure();
         fFigureDbcClassAttributeCompartmentRectangle
               .setBorder(new MarginBorder(getMapMode().DPtoLP(0), getMapMode()
                     .DPtoLP(5), getMapMode().DPtoLP(5), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcClassAttributeCompartmentRectangle = new GridData();
         constraintFFigureDbcClassAttributeCompartmentRectangle.verticalAlignment = GridData.BEGINNING;
         constraintFFigureDbcClassAttributeCompartmentRectangle.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcClassAttributeCompartmentRectangle.horizontalIndent = 0;
         constraintFFigureDbcClassAttributeCompartmentRectangle.horizontalSpan = 1;
         constraintFFigureDbcClassAttributeCompartmentRectangle.verticalSpan = 1;
         constraintFFigureDbcClassAttributeCompartmentRectangle.grabExcessHorizontalSpace = true;
         constraintFFigureDbcClassAttributeCompartmentRectangle.grabExcessVerticalSpace = false;
         this.add(fFigureDbcClassAttributeCompartmentRectangle,
               constraintFFigureDbcClassAttributeCompartmentRectangle);

         fFigureDbcClassAttributeCompartmentRectangle
               .setLayoutManager(new StackLayout());

         fFigureDbcClassMainCompartmentRectangle = new RectangleFigure();
         fFigureDbcClassMainCompartmentRectangle.setBorder(new MarginBorder(
               getMapMode().DPtoLP(0), getMapMode().DPtoLP(5), getMapMode()
                     .DPtoLP(5), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcClassMainCompartmentRectangle = new GridData();
         constraintFFigureDbcClassMainCompartmentRectangle.verticalAlignment = GridData.FILL;
         constraintFFigureDbcClassMainCompartmentRectangle.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcClassMainCompartmentRectangle.horizontalIndent = 0;
         constraintFFigureDbcClassMainCompartmentRectangle.horizontalSpan = 1;
         constraintFFigureDbcClassMainCompartmentRectangle.verticalSpan = 1;
         constraintFFigureDbcClassMainCompartmentRectangle.grabExcessHorizontalSpace = true;
         constraintFFigureDbcClassMainCompartmentRectangle.grabExcessVerticalSpace = true;
         this.add(fFigureDbcClassMainCompartmentRectangle,
               constraintFFigureDbcClassMainCompartmentRectangle);

      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcClassNameFigure() {
         return fFigureDbcClassNameFigure;
      }

      /**
       * @generated
       */
      public RectangleFigure getFigureDbcClassAttributeCompartmentRectangle() {
         return fFigureDbcClassAttributeCompartmentRectangle;
      }

      /**
       * @generated
       */
      public RectangleFigure getFigureDbcClassMainCompartmentRectangle() {
         return fFigureDbcClassMainCompartmentRectangle;
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