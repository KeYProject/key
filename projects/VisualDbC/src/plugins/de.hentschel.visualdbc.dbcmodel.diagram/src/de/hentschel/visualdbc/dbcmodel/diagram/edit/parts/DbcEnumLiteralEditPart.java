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
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.GridData;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.transaction.RunnableWithResult;
import org.eclipse.gef.AccessibleEditPart;
import org.eclipse.gef.DragTracker;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;
import org.eclipse.gef.requests.CreateRequest;
import org.eclipse.gef.requests.DirectEditRequest;
import org.eclipse.gef.requests.SelectionRequest;
import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParser;
import org.eclipse.gmf.runtime.common.ui.services.parser.IParserEditStatus;
import org.eclipse.gmf.runtime.common.ui.services.parser.ParserEditStatus;
import org.eclipse.gmf.runtime.common.ui.services.parser.ParserOptions;
import org.eclipse.gmf.runtime.diagram.ui.editparts.CompartmentEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITextAwareEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.LabelDirectEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.ListItemComponentEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.l10n.DiagramColorRegistry;
import org.eclipse.gmf.runtime.diagram.ui.requests.RequestConstants;
import org.eclipse.gmf.runtime.diagram.ui.tools.DragEditPartsTrackerEx;
import org.eclipse.gmf.runtime.diagram.ui.tools.TextDirectEditManager;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.draw2d.ui.figures.WrappingLabel;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.ui.services.parser.ISemanticParser;
import org.eclipse.gmf.runtime.gef.ui.figures.DefaultSizeNodeFigure;
import org.eclipse.gmf.runtime.gef.ui.figures.NodeFigure;
import org.eclipse.gmf.runtime.notation.FontStyle;
import org.eclipse.gmf.runtime.notation.NotationPackage;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.viewers.ICellEditorValidator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.accessibility.AccessibleEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCTextNonResizableEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbCTextSelectionEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcEnumLiteralItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCParserProvider;

/**
 * @generated
 */
public class DbcEnumLiteralEditPart extends ShapeNodeEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 3020;

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
   public DbcEnumLiteralEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcEnumLiteralItemSemanticEditPolicy());
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
      return primaryShape = new DbcEnumLiteralFigure();
   }

   /**
    * @generated
    */
   public DbcEnumLiteralFigure getPrimaryShape() {
      return (DbcEnumLiteralFigure) primaryShape;
   }

   /**
    * @generated
    */
   protected boolean addFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcEnumLiteralNameEditPart) {
         ((DbcEnumLiteralNameEditPart) childEditPart)
               .setLabel(getPrimaryShape().getFigureDbcEnumLiteralNameFigure());
         return true;
      }
      return false;
   }

   /**
    * @generated
    */
   protected boolean removeFixedChild(EditPart childEditPart) {
      if (childEditPart instanceof DbcEnumLiteralNameEditPart) {
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
      DefaultSizeNodeFigure result = new DefaultSizeNodeFigure(0, 18);
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
            .getType(DbcEnumLiteralNameEditPart.VISUAL_ID));
   }

   /**
    * @generated
    */
   public List<IElementType> getMARelTypesOnTarget() {
      ArrayList<IElementType> types = new ArrayList<IElementType>(1);
      types.add(DbCElementTypes.DbcProofReference_4002);
      return types;
   }

   /**
    * @generated
    */
   public List<IElementType> getMATypesForSource(IElementType relationshipType) {
      LinkedList<IElementType> types = new LinkedList<IElementType>();
      if (relationshipType == DbCElementTypes.DbcProofReference_4002) {
         types.add(DbCElementTypes.DbcProof_2014);
         types.add(DbCElementTypes.DbcProof_3034);
      }
      return types;
   }

   /**
    * @generated
    */
   public class DbcEnumLiteralFigure extends RectangleFigure {
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
      private WrappingLabel fFigureDbcEnumLiteralNameFigure;

      /**
       * @generated
       */
      public DbcEnumLiteralFigure() {

         GridLayout layoutThis = new GridLayout();
         layoutThis.numColumns = 1;
         layoutThis.makeColumnsEqualWidth = true;
         layoutThis.horizontalSpacing = 0;
         layoutThis.verticalSpacing = -1;
         layoutThis.marginWidth = 0;
         layoutThis.marginHeight = 0;
         this.setLayoutManager(layoutThis);

         this.setForegroundColor(THIS_FORE);
         this.setBackgroundColor(THIS_BACK);
         this.setPreferredSize(new Dimension(getMapMode().DPtoLP(0),
               getMapMode().DPtoLP(18)));

         this.setBorder(new MarginBorder(getMapMode().DPtoLP(0), getMapMode()
               .DPtoLP(0), getMapMode().DPtoLP(0), getMapMode().DPtoLP(0)));
         createContents();
      }

      /**
       * @generated
       */
      private void createContents() {

         fFigureDbcEnumLiteralNameFigure = new WrappingLabel();
         fFigureDbcEnumLiteralNameFigure.setText("<...>");
         fFigureDbcEnumLiteralNameFigure.setBorder(new MarginBorder(
               getMapMode().DPtoLP(0), getMapMode().DPtoLP(0), getMapMode()
                     .DPtoLP(0), getMapMode().DPtoLP(5)));

         GridData constraintFFigureDbcEnumLiteralNameFigure = new GridData();
         constraintFFigureDbcEnumLiteralNameFigure.verticalAlignment = GridData.CENTER;
         constraintFFigureDbcEnumLiteralNameFigure.horizontalAlignment = GridData.BEGINNING;
         constraintFFigureDbcEnumLiteralNameFigure.horizontalIndent = 0;
         constraintFFigureDbcEnumLiteralNameFigure.horizontalSpan = 0;
         constraintFFigureDbcEnumLiteralNameFigure.verticalSpan = 0;
         constraintFFigureDbcEnumLiteralNameFigure.grabExcessHorizontalSpace = false;
         constraintFFigureDbcEnumLiteralNameFigure.grabExcessVerticalSpace = true;
         this.add(fFigureDbcEnumLiteralNameFigure,
               constraintFFigureDbcEnumLiteralNameFigure);

      }

      /**
       * @generated
       */
      public WrappingLabel getFigureDbcEnumLiteralNameFigure() {
         return fFigureDbcEnumLiteralNameFigure;
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
      }
      
      /**
       * @generated NOT
       */
      public void disableHighlighting() {
         if (originalForegroundColor != null) {
            super.setForegroundColor(originalForegroundColor);
            super.setLineWidth(originalLineWidth);
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
   static final Color THIS_FORE = new Color(null, 240, 240, 250);

   /**
    * @generated
    */
   static final Color THIS_BACK = new Color(null, 240, 240, 250);

}