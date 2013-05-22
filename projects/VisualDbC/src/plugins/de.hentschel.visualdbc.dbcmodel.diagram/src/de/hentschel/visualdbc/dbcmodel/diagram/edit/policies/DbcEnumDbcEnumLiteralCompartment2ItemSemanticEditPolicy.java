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

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbcEnumLiteralCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcEnumDbcEnumLiteralCompartment2ItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcEnumDbcEnumLiteralCompartment2ItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcEnum_2013);
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      if (DbCElementTypes.DbcEnumLiteral_3020 == req.getElementType()) {
         return getGEFWrapper(new DbcEnumLiteralCreateCommand(req));
      }
      return super.getCreateCommand(req);
   }

}