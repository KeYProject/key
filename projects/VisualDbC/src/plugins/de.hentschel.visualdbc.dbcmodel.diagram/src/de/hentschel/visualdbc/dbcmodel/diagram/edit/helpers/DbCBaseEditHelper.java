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

package de.hentschel.visualdbc.dbcmodel.diagram.edit.helpers;

import org.eclipse.gmf.runtime.common.core.command.CompositeCommand;
import org.eclipse.gmf.runtime.common.core.command.ICommand;
import org.eclipse.gmf.runtime.emf.type.core.ElementTypeRegistry;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.type.core.edithelper.AbstractEditHelper;
import org.eclipse.gmf.runtime.emf.type.core.edithelper.IEditHelperAdvice;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyReferenceRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.IEditCommandRequest;

/**
 * @generated
 */
public class DbCBaseEditHelper extends AbstractEditHelper {

   /**
    * @generated
    */
   public static final String EDIT_POLICY_COMMAND = "edit policy command"; //$NON-NLS-1$

   /**
    * @generated
    */
   public static final String CONTEXT_ELEMENT_TYPE = "context element type"; //$NON-NLS-1$

   /**
    * @generated
    */
   protected IEditHelperAdvice[] getEditHelperAdvice(IEditCommandRequest req) {
      if (req.getParameter(CONTEXT_ELEMENT_TYPE) instanceof IElementType) {
         return ElementTypeRegistry.getInstance().getEditHelperAdvice(
               (IElementType) req.getParameter(CONTEXT_ELEMENT_TYPE));
      }
      return super.getEditHelperAdvice(req);
   }

   /**
    * @generated
    */
   protected ICommand getInsteadCommand(IEditCommandRequest req) {
      ICommand epCommand = (ICommand) req.getParameter(EDIT_POLICY_COMMAND);
      req.setParameter(EDIT_POLICY_COMMAND, null);
      ICommand ehCommand = super.getInsteadCommand(req);
      if (epCommand == null) {
         return ehCommand;
      }
      if (ehCommand == null) {
         return epCommand;
      }
      CompositeCommand command = new CompositeCommand(null);
      command.add(epCommand);
      command.add(ehCommand);
      return command;
   }

   /**
    * @generated
    */
   protected ICommand getCreateCommand(CreateElementRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected ICommand getCreateRelationshipCommand(CreateRelationshipRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected ICommand getDestroyElementCommand(DestroyElementRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected ICommand getDestroyReferenceCommand(DestroyReferenceRequest req) {
      return null;
   }
}