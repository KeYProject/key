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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcOperationContractCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProof2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcConstructorDbcConstructorCompartmentItemSemanticEditPolicy
      extends DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcConstructorDbcConstructorCompartmentItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcConstructor_3010);
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      if (DbCElementTypes.DbcProof_3034 == req.getElementType()) {
         return getGEFWrapper(new DbcProof2CreateCommand(req));
      }
      if (DbCElementTypes.DbcOperationContract_3026 == req.getElementType()) {
         return getGEFWrapper(new DbcOperationContractCreateCommand(req));
      }
      return super.getCreateCommand(req);
   }

}