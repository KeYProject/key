/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.dbcmodel.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcClass2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcEnum2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcInterface2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcInvariantCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcMethodCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProof2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcInterfaceDbcInterfaceMainCompartmentItemSemanticEditPolicy
      extends DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcInterfaceDbcInterfaceMainCompartmentItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcInterface_3032);
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      if (DbCElementTypes.DbcClass_3031 == req.getElementType()) {
         return getGEFWrapper(new DbcClass2CreateCommand(req));
      }
      if (DbCElementTypes.DbcInterface_3032 == req.getElementType()) {
         return getGEFWrapper(new DbcInterface2CreateCommand(req));
      }
      if (DbCElementTypes.DbcEnum_3033 == req.getElementType()) {
         return getGEFWrapper(new DbcEnum2CreateCommand(req));
      }
      if (DbCElementTypes.DbcProof_3034 == req.getElementType()) {
         return getGEFWrapper(new DbcProof2CreateCommand(req));
      }
      if (DbCElementTypes.DbcInvariant_3035 == req.getElementType()) {
         return getGEFWrapper(new DbcInvariantCreateCommand(req));
      }
      if (DbCElementTypes.DbcMethod_3009 == req.getElementType()) {
         return getGEFWrapper(new DbcMethodCreateCommand(req));
      }
      return super.getCreateCommand(req);
   }

}
