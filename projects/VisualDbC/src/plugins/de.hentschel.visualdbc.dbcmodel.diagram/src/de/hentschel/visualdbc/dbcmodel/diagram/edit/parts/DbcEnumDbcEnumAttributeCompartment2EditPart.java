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

import org.eclipse.draw2d.IFigure;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ListCompartmentEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.CreationEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.DragDropEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.EditPolicyRoles;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.ResizableCompartmentEditPolicy;
import org.eclipse.gmf.runtime.diagram.ui.figures.ResizableCompartmentFigure;
import org.eclipse.gmf.runtime.draw2d.ui.figures.ConstrainedToolbarLayout;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcEnumDbcEnumAttributeCompartment2CanonicalEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.policies.DbcEnumDbcEnumAttributeCompartment2ItemSemanticEditPolicy;
import de.hentschel.visualdbc.dbcmodel.diagram.part.Messages;

/**
 * @generated
 */
public class DbcEnumDbcEnumAttributeCompartment2EditPart extends
      ListCompartmentEditPart {

   /**
    * @generated
    */
   public static final int VISUAL_ID = 7062;

   /**
    * @generated
    */
   public DbcEnumDbcEnumAttributeCompartment2EditPart(View view) {
      super(view);
   }

   /**
    * @generated
    */
   protected boolean hasModelChildrenChanged(Notification evt) {
      return false;
   }

   /**
    * @generated
    */
   public String getCompartmentName() {
      return Messages.DbcEnumDbcEnumAttributeCompartment2EditPart_title;
   }

   /**
    * @generated
    */
   public IFigure createFigure() {
      ResizableCompartmentFigure result = (ResizableCompartmentFigure) super
            .createFigure();
      result.setTitleVisibility(false);
      return result;
   }

   /**
    * @generated
    */
   protected void createDefaultEditPolicies() {
      super.createDefaultEditPolicies();
      installEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE,
            new ResizableCompartmentEditPolicy());
      installEditPolicy(EditPolicyRoles.SEMANTIC_ROLE,
            new DbcEnumDbcEnumAttributeCompartment2ItemSemanticEditPolicy());
      installEditPolicy(EditPolicyRoles.CREATION_ROLE, new CreationEditPolicy());
      installEditPolicy(EditPolicyRoles.DRAG_DROP_ROLE,
            new DragDropEditPolicy());
      installEditPolicy(EditPolicyRoles.CANONICAL_ROLE,
            new DbcEnumDbcEnumAttributeCompartment2CanonicalEditPolicy());
   }

   /**
    * @generated
    */
   protected void setRatio(Double ratio) {
      if (getFigure().getParent().getLayoutManager() instanceof ConstrainedToolbarLayout) {
         super.setRatio(ratio);
      }
   }

}