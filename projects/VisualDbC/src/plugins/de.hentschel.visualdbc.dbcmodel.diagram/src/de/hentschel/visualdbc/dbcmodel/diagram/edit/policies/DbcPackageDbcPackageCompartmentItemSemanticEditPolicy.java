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

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcClass2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcEnum2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcInterface2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcPackage2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcProof2CreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcPackageDbcPackageCompartmentItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcPackageDbcPackageCompartmentItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcPackage_2007);
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      if (DbCElementTypes.DbcPackage_3027 == req.getElementType()) {
         return getGEFWrapper(new DbcPackage2CreateCommand(req));
      }
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
      return super.getCreateCommand(req);
   }

}