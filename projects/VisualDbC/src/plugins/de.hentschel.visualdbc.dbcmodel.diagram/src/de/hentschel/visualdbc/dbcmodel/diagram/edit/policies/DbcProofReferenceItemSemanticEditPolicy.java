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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;

import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcProofReferenceItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcProofReferenceItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcProofReference_4002);
   }

   /**
    * @generated
    */
   protected Command getDestroyElementCommand(DestroyElementRequest req) {
      return getGEFWrapper(new DestroyElementCommand(req));
   }

}