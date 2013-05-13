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

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcEnum2ItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcEnum2EditPart extends ShapeNodeEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 3033;

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
   public DbcEnum2EditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      installEditPolicy(EditPolicyRoles.CREATION_ROLE, new CreationEditPolicy());
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcEnum2ItemSemanticEditPolicy());
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
      return primaryShape = new DbcEnumFigure();
   }

   /**
    * @generated
    */
   public DbcEnumFigure getPrimaryShape() {
      return (DbcEnumFigure) primaryShape;
   }

   /**
    * @generated
    */
   protected boolean addFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcEnumName2EditPart) {
         ((DbcEnumName2EditPart) childEditPart).setLabel(getPrimaryShape()
               .getFigureDbcEnumNameFigure());
         return true;
      }
      if (childEditPart instanceof DbcEnumDbcEnumMainCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcEnumMainCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.add(((DbcEnumDbcEnumMainCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      if (childEditPart instanceof DbcEnumDbcEnumAttributeCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcEnumAttributeCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.add(((DbcEnumDbcEnumAttributeCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      if (childEditPart instanceof DbcEnumDbcEnumLiteralCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcEnumLiteralCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.add(((DbcEnumDbcEnumLiteralCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean removeFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcEnumName2EditPart) {
         return true;
      }
      if (childEditPart instanceof DbcEnumDbcEnumMainCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcEnumMainCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.remove(((DbcEnumDbcEnumMainCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      if (childEditPart instanceof DbcEnumDbcEnumAttributeCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcEnumAttributeCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.remove(((DbcEnumDbcEnumAttributeCompartmentEditPart) childEditPart)
               .getFigure());
         return true;
      }
      if (childEditPart instanceof DbcEnumDbcEnumLiteralCompartmentEditPart) {
         IFigure pane = getPrimaryShape()
               .getFigureDbcEnumLiteralCompartmentRectangle();
         setupContentPane(pane); // FIXME each comparment should handle his content pane in his own way 
         pane.remove(((DbcEnumDbcEnumLiteralCompartmentEditPart) childEditPart)
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
      if (editPart instanceof DbcEnumDbcEnumMainCompartmentEditPart) {
         return getPrimaryShape().getFigureDbcEnumMainCompartmentRectangle();
      }
      if (editPart instanceof DbcEnumDbcEnumAttributeCompartmentEditPart) {
         return getPrimaryShape()
               .getFigureDbcEnumAttributeCompartmentRectangle();
      }
      if (editPart instanceof DbcEnumDbcEnumLiteralCompartmentEditPart) {
         return getPrimaryShape().getFigureDbcEnumLiteralCompartmentRectangle();
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
            .getType(DbcEnumName2EditPart.VISUAL_ID));
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnSource() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(1);
      types.add(DbCElementTypes.AbstractDbcClassImplements_4005);
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnSourceAndTarget(
         IGraphicalEditPart targetEditPart) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
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
      if (relationshipType == DbCElementTypes.AbstractDbcClassImplements_4005) {
         types.add(DbCElementTypes.DbcInterface_2011);
         types.add(DbCElementTypes.DbcInterface_3032);
      }
      return types;
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
   public EditPart getTargetEditPart(Request request) {
      if (request instanceof CreateViewAndElementRequest) {
         CreateElementRequestAdapter adapter = ((CreateViewAndElementRequest) request)
               .getViewAndElementDescriptor().getCreateElementRequestAdapter();
         IElementType type = (IElementType) adapter
               .getAdapter(IElementType.class);
         if (type == DbCElementTypes.DbcAttribute_3011) {
            return getChildBySemanticHint(DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumAttributeCompartmentEditPart.VISUAL_ID));
         }
         if (type == DbCElementTypes.DbcEnumLiteral_3020) {
            return getChildBySemanticHint(DbCVisualIDRegistry
                  .getType(DbcEnumDbcEnumLiteralCompartmentEditPart.VISUAL_ID));
         }
      }
      return super.getTargetEditPart(request);
   }

   /**
    * @generated
    */
   public class DbcEnumFigure extends RectangleFigure {
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
      private WrappingLabel fFigureDbcEnumNameFigure;
      /**
       * @generated
       */
      private RectangleFigure fFigureDbcEnumAttributeCompartmentRectangle;
      /**
       * @generated
       */
      private RectangleFigure fFigureDbcEnumMainCompartmentRectangle;
      /**
       * @generated
       */
      private RectangleFigure fFigureDbcEnumLiteralCompartmentRectangle;

      /**
       * @generated
       */
      public DbcEnumFigure() {

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

         fFigureDbcEnumNameFigure = new WrappingLabel();
         fFigureDbcEnumNameFigure.setText("<...>");
         fFigureDbcEnumNameFigure.setBorder(new MarginBorder(getMapMode()
               .DPtoLP(5), getMapMode().DPtoLP(5), getMapMode().DPtoLP(3),
               getMapMode().DPtoLP(5)));

         this.add(fFigureDbcEnumNameFigure);

         fFigureDbcEnumLiteralCompartmentRectangle = new RectangleFigure();
         fFigureDbcEnumLiteralCompartmentRectangle.setBorder(new MarginBorder(
               getMapMode().DPtoLP(0), getMapMode().DPtoLP(5), getMapMode()
                     .DPtoLP(5), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcEnumLiteralCompartmentRectangle = new GridData();
         constraintFFigureDbcEnumLiteralCompartmentRectangle.verticalAlignment = GridData.BEGINNING;
         constraintFFigureDbcEnumLiteralCompartmentRectangle.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcEnumLiteralCompartmentRectangle.horizontalIndent = 0;
         constraintFFigureDbcEnumLiteralCompartmentRectangle.horizontalSpan = 1;
         constraintFFigureDbcEnumLiteralCompartmentRectangle.verticalSpan = 1;
         constraintFFigureDbcEnumLiteralCompartmentRectangle.grabExcessHorizontalSpace = true;
         constraintFFigureDbcEnumLiteralCompartmentRectangle.grabExcessVerticalSpace = false;
         this.add(fFigureDbcEnumLiteralCompartmentRectangle,
               constraintFFigureDbcEnumLiteralCompartmentRectangle);

         fFigureDbcEnumLiteralCompartmentRectangle
               .setLayoutManager(new StackLayout());

         fFigureDbcEnumAttributeCompartmentRectangle = new RectangleFigure();
         fFigureDbcEnumAttributeCompartmentRectangle
               .setBorder(new MarginBorder(getMapMode().DPtoLP(0), getMapMode()
                     .DPtoLP(5), getMapMode().DPtoLP(5), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcEnumAttributeCompartmentRectangle = new GridData();
         constraintFFigureDbcEnumAttributeCompartmentRectangle.verticalAlignment = GridData.BEGINNING;
         constraintFFigureDbcEnumAttributeCompartmentRectangle.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcEnumAttributeCompartmentRectangle.horizontalIndent = 0;
         constraintFFigureDbcEnumAttributeCompartmentRectangle.horizontalSpan = 1;
         constraintFFigureDbcEnumAttributeCompartmentRectangle.verticalSpan = 1;
         constraintFFigureDbcEnumAttributeCompartmentRectangle.grabExcessHorizontalSpace = true;
         constraintFFigureDbcEnumAttributeCompartmentRectangle.grabExcessVerticalSpace = false;
         this.add(fFigureDbcEnumAttributeCompartmentRectangle,
               constraintFFigureDbcEnumAttributeCompartmentRectangle);

         fFigureDbcEnumAttributeCompartmentRectangle
               .setLayoutManager(new StackLayout());

         fFigureDbcEnumMainCompartmentRectangle = new RectangleFigure();
         fFigureDbcEnumMainCompartmentRectangle.setBorder(new MarginBorder(
               getMapMode().DPtoLP(0), getMapMode().DPtoLP(5), getMapMode()
                     .DPtoLP(5), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcEnumMainCompartmentRectangle = new GridData();
         constraintFFigureDbcEnumMainCompartmentRectangle.verticalAlignment = GridData.FILL;
         constraintFFigureDbcEnumMainCompartmentRectangle.horizontalAlignment = GridData.FILL;
         constraintFFigureDbcEnumMainCompartmentRectangle.horizontalIndent = 0;
         constraintFFigureDbcEnumMainCompartmentRectangle.horizontalSpan = 1;
         constraintFFigureDbcEnumMainCompartmentRectangle.verticalSpan = 1;
         constraintFFigureDbcEnumMainCompartmentRectangle.grabExcessHorizontalSpace = true;
         constraintFFigureDbcEnumMainCompartmentRectangle.grabExcessVerticalSpace = true;
         this.add(fFigureDbcEnumMainCompartmentRectangle,
               constraintFFigureDbcEnumMainCompartmentRectangle);

      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcEnumNameFigure() {
         return fFigureDbcEnumNameFigure;
      }

      /**
       * @generated
       */
      public RectangleFigure getFigureDbcEnumAttributeCompartmentRectangle() {
         return fFigureDbcEnumAttributeCompartmentRectangle;
      }

      /**
       * @generated
       */
      public RectangleFigure getFigureDbcEnumMainCompartmentRectangle() {
         return fFigureDbcEnumMainCompartmentRectangle;
      }

      /**
       * @generated
       */
      public RectangleFigure getFigureDbcEnumLiteralCompartmentRectangle() {
         return fFigureDbcEnumLiteralCompartmentRectangle;
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