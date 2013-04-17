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

import org.eclipse.draw2d.Connection;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.PolylineDecoration;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.geometry.PointList;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ConnectionNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITreeBranchEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.draw2d.ui.figures.PolylineConnectionEx;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcProofReferenceItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcProofReferenceEditPart extends ConnectionNodeEditPart implements
      ITreeBranchEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 4002;

   /**
    * @generated
    */
   public DbcProofReferenceEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcProofReferenceItemSemanticEditPolicy());
   }

   /**
    * Creates figure for this edit part.
    * 
    * Body of this method does not depend on settings in generation model
    * so you may safely remove <i>generated</i> tag and modify it.
    * 
    * @generated
    */

   protected Connection createConnectionFigure() {
      return new DbcProofReferenceFigure();
   }

   /**
    * @generated
    */
   public DbcProofReferenceFigure getPrimaryShape() {
      return (DbcProofReferenceFigure) getFigure();
   }

   /**
    * @generated
    */
   public class DbcProofReferenceFigure extends PolylineConnectionEx {
      /**
       * @generated NOT
       */
      private boolean globalVisible = true; // Required for automaitc proof reference hiding

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
      public DbcProofReferenceFigure() {
         this.setLineStyle(Graphics.LINE_DASH);

         setTargetDecoration(createTargetDecoration());
      }

      /**
       * @generated
       */
      private RotatableDecoration createTargetDecoration() {
         PolylineDecoration df = new PolylineDecoration();
         PointList pl = new PointList();
         pl.addPoint(getMapMode().DPtoLP(-1), getMapMode().DPtoLP(-1));
         pl.addPoint(getMapMode().DPtoLP(0), getMapMode().DPtoLP(0));
         pl.addPoint(getMapMode().DPtoLP(-1), getMapMode().DPtoLP(1));
         df.setTemplate(pl);
         df.setScale(getMapMode().DPtoLP(7), getMapMode().DPtoLP(3));
         return df;
      }

      /**
       * @generated NOT
       */
      @Override
      public boolean isVisible() {
         return isGlobalVisible() && super.isVisible();
      }

      /**
       * @generated NOT
       */
      public boolean isGlobalVisible() {
         return globalVisible;
      }

      /**
       * @generated NOT
       */
      public void setGlobalVisible(boolean globalVisible) {
         this.globalVisible = globalVisible;
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

}