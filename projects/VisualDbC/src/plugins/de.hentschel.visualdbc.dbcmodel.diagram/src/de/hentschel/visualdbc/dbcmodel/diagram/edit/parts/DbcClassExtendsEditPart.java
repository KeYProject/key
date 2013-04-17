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
import org.eclipse.draw2d.PolygonDecoration;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.geometry.PointList;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ConnectionNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITreeBranchEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.draw2d.ui.figures.PolylineConnectionEx;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.swt.graphics.Color;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcClassExtendsItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcClassExtendsEditPart extends ConnectionNodeEditPart implements
      ITreeBranchEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 4003;

   /**
    * @generated
    */
   public DbcClassExtendsEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcClassExtendsItemSemanticEditPolicy());
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
      return new ExtendsFigure();
   }

   /**
    * @generated
    */
   public ExtendsFigure getPrimaryShape() {
      return (ExtendsFigure) getFigure();
   }

   /**
    * @generated
    */
   public class ExtendsFigure extends PolylineConnectionEx {

      /**
       * @generated
       */
      public ExtendsFigure() {

         setTargetDecoration(createTargetDecoration());
      }

      /**
       * @generated
       */
      private RotatableDecoration createTargetDecoration() {
         PolygonDecoration df = new PolygonDecoration();
         df.setFill(true);
         df.setBackgroundColor(DF_BACK);
         PointList pl = new PointList();
         pl.addPoint(getMapMode().DPtoLP(-2), getMapMode().DPtoLP(-2));
         pl.addPoint(getMapMode().DPtoLP(0), getMapMode().DPtoLP(0));
         pl.addPoint(getMapMode().DPtoLP(-2), getMapMode().DPtoLP(2));
         pl.addPoint(getMapMode().DPtoLP(-2), getMapMode().DPtoLP(-2));
         df.setTemplate(pl);
         df.setScale(getMapMode().DPtoLP(7), getMapMode().DPtoLP(3));
         return df;
      }

   }

   /**
    * @generated
    */
   static final Color DF_BACK = new Color(null, 255, 255, 255);

}