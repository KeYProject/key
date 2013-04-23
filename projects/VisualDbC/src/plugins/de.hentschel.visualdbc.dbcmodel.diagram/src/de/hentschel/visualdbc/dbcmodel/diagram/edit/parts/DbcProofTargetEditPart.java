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
import org.eclipse.draw2d.PolylineDecoration;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.geometry.PointList;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ConnectionNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ITreeBranchEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.draw2d.ui.figures.PolylineConnectionEx;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcProofTargetItemSemanticEditPolicy;

/**
 * @generated
 */
public class DbcProofTargetEditPart extends ConnectionNodeEditPart implements
      ITreeBranchEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 4001;

   /**
    * @generated
    */
   public DbcProofTargetEditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcProofTargetItemSemanticEditPolicy());
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
      return new DbcProofTargetFigure();
   }

   /**
    * @generated
    */
   public DbcProofTargetFigure getPrimaryShape() {
      return (DbcProofTargetFigure) getFigure();
   }

   /**
    * @generated
    */
   public class DbcProofTargetFigure extends PolylineConnectionEx {

      /**
       * @generated
       */
      public DbcProofTargetFigure() {

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

   }

}