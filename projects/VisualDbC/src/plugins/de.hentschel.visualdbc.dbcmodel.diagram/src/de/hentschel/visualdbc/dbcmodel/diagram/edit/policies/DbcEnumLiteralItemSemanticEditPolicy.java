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

import org.eclipse.emf.ecore.EAnnotation;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand;
import org.eclipse.gmf.runtime.emf.commands.core.command.CompositeTransactionalCommand;
import org.eclipse.gmf.runtime.emf.type.core.commands.DestroyElementCommand;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcEnumLiteralItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcEnumLiteralItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcEnumLiteral_3020);
   }

   /**
    * @generated
    */
   protected Command getDestroyElementCommand(DestroyElementRequest req) {
      View view = (View) getHost().getModel();
      CompositeTransactionalCommand cmd = new CompositeTransactionalCommand(
            getEditingDomain(), null);
      cmd.setTransactionNestingEnabled(false);
      EAnnotation annotation = view.getEAnnotation("Shortcut"); //$NON-NLS-1$
      if (annotation == null) {
         // there are indirectly referenced children, need extra commands: false
         addDestroyShortcutsCommand(cmd, view);
         // delete host element
         cmd.add(new DestroyElementCommand(req));
      }
      else {
         cmd.add(new DeleteCommand(getEditingDomain(), view));
      }
      return getGEFWrapper(cmd.reduce());
   }

}
