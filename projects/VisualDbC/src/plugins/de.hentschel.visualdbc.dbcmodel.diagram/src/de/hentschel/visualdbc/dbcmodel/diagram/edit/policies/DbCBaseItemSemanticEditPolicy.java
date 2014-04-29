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

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.commands.UnexecutableCommand;
import org.eclipse.gef.requests.ReconnectRequest;
import org.eclipse.gmf.runtime.common.core.command.ICommand;
import org.eclipse.gmf.runtime.common.core.command.ICompositeCommand;
import org.eclipse.gmf.runtime.diagram.core.commands.DeleteCommand;
import org.eclipse.gmf.runtime.diagram.ui.commands.CommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.editpolicies.SemanticEditPolicy;
import org.eclipse.gmf.runtime.emf.commands.core.command.CompositeTransactionalCommand;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.type.core.requests.ConfigureRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyElementRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyReferenceRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DestroyRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.DuplicateElementsRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.GetEditContextRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.IEditCommandRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.MoveRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientReferenceRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.ReorientRelationshipRequest;
import org.eclipse.gmf.runtime.emf.type.core.requests.SetRequest;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.helpers.DbCBaseEditHelper;
import de.hentschel.visualdbc.dbcmodel.diagram.expressions.DbCOCLFactory;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbCBaseItemSemanticEditPolicy extends SemanticEditPolicy {

   /**
    * Extended request data key to hold editpart visual id.
    * @generated
    */
   public static final String VISUAL_ID_KEY = "visual_id"; //$NON-NLS-1$

   /**
    * @generated
    */
   private final IElementType myElementType;

   /**
    * @generated
    */
   protected DbCBaseItemSemanticEditPolicy(IElementType elementType) {
      myElementType = elementType;
   }

   /**
    * Extended request data key to hold editpart visual id.
    * Add visual id of edited editpart to extended data of the request
    * so command switch can decide what kind of diagram element is being edited.
    * It is done in those cases when it's not possible to deduce diagram
    * element kind from domain element.
    * 
    * @generated
    */
   public Command getCommand(Request request) {
      if (request instanceof ReconnectRequest) {
         Object view = ((ReconnectRequest) request).getConnectionEditPart()
               .getModel();
         if (view instanceof View) {
            Integer id = new Integer(
                  DbCVisualIDRegistry.getVisualID((View) view));
            request.getExtendedData().put(VISUAL_ID_KEY, id);
         }
      }
      return super.getCommand(request);
   }

   /**
    * Returns visual id from request parameters.
    * @generated
    */
   protected int getVisualID(IEditCommandRequest request) {
      Object id = request.getParameter(VISUAL_ID_KEY);
      return id instanceof Integer ? ((Integer) id).intValue() : -1;
   }

   /**
    * @generated
    */
   protected Command getSemanticCommand(IEditCommandRequest request) {
      IEditCommandRequest completedRequest = completeRequest(request);
      Command semanticCommand = getSemanticCommandSwitch(completedRequest);
      semanticCommand = getEditHelperCommand(completedRequest, semanticCommand);
      if (completedRequest instanceof DestroyRequest) {
         DestroyRequest destroyRequest = (DestroyRequest) completedRequest;
         return shouldProceed(destroyRequest) ? addDeleteViewCommand(
               semanticCommand, destroyRequest) : null;
      }
      return semanticCommand;
   }

   /**
    * @generated
    */
   protected Command addDeleteViewCommand(Command mainCommand,
         DestroyRequest completedRequest) {
      Command deleteViewCommand = getGEFWrapper(new DeleteCommand(
            getEditingDomain(), (View) getHost().getModel()));
      return mainCommand == null ? deleteViewCommand : mainCommand
            .chain(deleteViewCommand);
   }

   /**
    * @generated
    */
   private Command getEditHelperCommand(IEditCommandRequest request,
         Command editPolicyCommand) {
      if (editPolicyCommand != null) {
         ICommand command = editPolicyCommand instanceof ICommandProxy ? ((ICommandProxy) editPolicyCommand)
               .getICommand() : new CommandProxy(editPolicyCommand);
         request.setParameter(DbCBaseEditHelper.EDIT_POLICY_COMMAND, command);
      }
      IElementType requestContextElementType = getContextElementType(request);
      request.setParameter(DbCBaseEditHelper.CONTEXT_ELEMENT_TYPE,
            requestContextElementType);
      ICommand command = requestContextElementType.getEditCommand(request);
      request.setParameter(DbCBaseEditHelper.EDIT_POLICY_COMMAND, null);
      request.setParameter(DbCBaseEditHelper.CONTEXT_ELEMENT_TYPE, null);
      if (command != null) {
         if (!(command instanceof CompositeTransactionalCommand)) {
            command = new CompositeTransactionalCommand(getEditingDomain(),
                  command.getLabel()).compose(command);
         }
         return new ICommandProxy(command);
      }
      return editPolicyCommand;
   }

   /**
    * @generated
    */
   private IElementType getContextElementType(IEditCommandRequest request) {
      IElementType requestContextElementType = DbCElementTypes
            .getElementType(getVisualID(request));
      return requestContextElementType != null ? requestContextElementType
            : myElementType;
   }

   /**
    * @generated
    */
   protected Command getSemanticCommandSwitch(IEditCommandRequest req) {
      if (req instanceof CreateRelationshipRequest) {
         return getCreateRelationshipCommand((CreateRelationshipRequest) req);
      }
      else if (req instanceof CreateElementRequest) {
         return getCreateCommand((CreateElementRequest) req);
      }
      else if (req instanceof ConfigureRequest) {
         return getConfigureCommand((ConfigureRequest) req);
      }
      else if (req instanceof DestroyElementRequest) {
         return getDestroyElementCommand((DestroyElementRequest) req);
      }
      else if (req instanceof DestroyReferenceRequest) {
         return getDestroyReferenceCommand((DestroyReferenceRequest) req);
      }
      else if (req instanceof DuplicateElementsRequest) {
         return getDuplicateCommand((DuplicateElementsRequest) req);
      }
      else if (req instanceof GetEditContextRequest) {
         return getEditContextCommand((GetEditContextRequest) req);
      }
      else if (req instanceof MoveRequest) {
         return getMoveCommand((MoveRequest) req);
      }
      else if (req instanceof ReorientReferenceRelationshipRequest) {
         return getReorientReferenceRelationshipCommand((ReorientReferenceRelationshipRequest) req);
      }
      else if (req instanceof ReorientRelationshipRequest) {
         return getReorientRelationshipCommand((ReorientRelationshipRequest) req);
      }
      else if (req instanceof SetRequest) {
         return getSetCommand((SetRequest) req);
      }
      return null;
   }

   /**
    * @generated
    */
   protected Command getConfigureCommand(ConfigureRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getCreateRelationshipCommand(CreateRelationshipRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getSetCommand(SetRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getEditContextCommand(GetEditContextRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getDestroyElementCommand(DestroyElementRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getDestroyReferenceCommand(DestroyReferenceRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getDuplicateCommand(DuplicateElementsRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getMoveCommand(MoveRequest req) {
      return null;
   }

   /**
    * @generated
    */
   protected Command getReorientReferenceRelationshipCommand(
         ReorientReferenceRelationshipRequest req) {
      return UnexecutableCommand.INSTANCE;
   }

   /**
    * @generated
    */
   protected Command getReorientRelationshipCommand(
         ReorientRelationshipRequest req) {
      return UnexecutableCommand.INSTANCE;
   }

   /**
    * @generated
    */
   protected final Command getGEFWrapper(ICommand cmd) {
      return new ICommandProxy(cmd);
   }

   /**
    * Returns editing domain from the host edit part.
    * @generated
    */
   protected TransactionalEditingDomain getEditingDomain() {
      return ((IGraphicalEditPart) getHost()).getEditingDomain();
   }

   /**
    * Clean all shortcuts to the host element from the same diagram
    * @generated
    */
   protected void addDestroyShortcutsCommand(ICompositeCommand cmd, View view) {
      assert view.getEAnnotation("Shortcut") == null; //$NON-NLS-1$
      for (Iterator it = view.getDiagram().getChildren().iterator(); it
            .hasNext();) {
         View nextView = (View) it.next();
         if (nextView.getEAnnotation("Shortcut") == null || !nextView.isSetElement() || nextView.getElement() != view.getElement()) { //$NON-NLS-1$
            continue;
         }
         cmd.add(new DeleteCommand(getEditingDomain(), nextView));
      }
   }

   /**
    * @generated
    */
   public static LinkConstraints getLinkConstraints() {
      LinkConstraints cached = DbCDiagramEditorPlugin.getInstance()
            .getLinkConstraints();
      if (cached == null) {
         DbCDiagramEditorPlugin.getInstance().setLinkConstraints(
               cached = new LinkConstraints());
      }
      return cached;
   }

   /**
    * @generated
    */
   public static class LinkConstraints {

      /**
       * @generated
       */
      LinkConstraints() {
         // use static method #getLinkConstraints() to access instance
      }

      /**
       * @generated
       */
      public boolean canCreateDbcProofTarget_4001(DbcProof source,
            IDbCProvable target) {
         if (source != null) {
            if (source.getTarget() != null) {
               return false;
            }
         }

         return canExistDbcProofTarget_4001(source, target);
      }

      /**
       * @generated
       */
      public boolean canCreateDbcProofReference_4002(DbcProof source,
            IDbCProofReferencable target) {
         return canExistDbcProofReference_4002(null, source, target);
      }

      /**
       * @generated
       */
      public boolean canCreateDbcClassExtends_4003(DbcClass source,
            DbcClass target) {
         if (source != null) {
            if (source.getExtends().contains(target)) {
               return false;
            }
         }

         return canExistDbcClassExtends_4003(source, target);
      }

      /**
       * @generated
       */
      public boolean canCreateDbcInterfaceExtends_4004(DbcInterface source,
            DbcInterface target) {
         if (source != null) {
            if (source.getExtends().contains(target)) {
               return false;
            }
         }

         return canExistDbcInterfaceExtends_4004(source, target);
      }

      /**
       * @generated
       */
      public boolean canCreateAbstractDbcClassImplements_4005(
            AbstractDbcClass source, DbcInterface target) {
         if (source != null) {
            if (source.getImplements().contains(target)) {
               return false;
            }
         }

         return canExistAbstractDbcClassImplements_4005(source, target);
      }

      /**
       * @generated
       */
      public boolean canExistDbcProofTarget_4001(DbcProof source,
            IDbCProvable target) {
         return true;
      }

      /**
       * @generated
       */
      public boolean canExistDbcProofReference_4002(
            DbcProofReference linkInstance, DbcProof source,
            IDbCProofReferencable target) {
         return true;
      }

      /**
       * @generated
       */
      public boolean canExistDbcClassExtends_4003(DbcClass source,
            DbcClass target) {
         try {
            if (target == null) {
               return true;
            }
            else {
               Map<String, EClassifier> env = Collections
                     .<String, EClassifier> singletonMap(
                           "oppositeEnd", DbcmodelPackage.eINSTANCE.getDbcClass()); //$NON-NLS-1$
               Object targetVal = DbCOCLFactory.getExpression(0,
                     DbcmodelPackage.eINSTANCE.getDbcClass(), env).evaluate(
                     target, Collections.singletonMap("oppositeEnd", source)); //$NON-NLS-1$
               if (false == targetVal instanceof Boolean
                     || !((Boolean) targetVal).booleanValue()) {
                  return false;
               } // else fall-through
            }
            return true;
         }
         catch (Exception e) {
            DbCDiagramEditorPlugin.getInstance().logError(
                  "Link constraint evaluation error", e); //$NON-NLS-1$
            return false;
         }
      }

      /**
       * @generated
       */
      public boolean canExistDbcInterfaceExtends_4004(DbcInterface source,
            DbcInterface target) {
         try {
            if (target == null) {
               return true;
            }
            else {
               Map<String, EClassifier> env = Collections
                     .<String, EClassifier> singletonMap(
                           "oppositeEnd", DbcmodelPackage.eINSTANCE.getDbcInterface()); //$NON-NLS-1$
               Object targetVal = DbCOCLFactory.getExpression(1,
                     DbcmodelPackage.eINSTANCE.getDbcInterface(), env)
                     .evaluate(target,
                           Collections.singletonMap("oppositeEnd", source)); //$NON-NLS-1$
               if (false == targetVal instanceof Boolean
                     || !((Boolean) targetVal).booleanValue()) {
                  return false;
               } // else fall-through
            }
            return true;
         }
         catch (Exception e) {
            DbCDiagramEditorPlugin.getInstance().logError(
                  "Link constraint evaluation error", e); //$NON-NLS-1$
            return false;
         }
      }

      /**
       * @generated
       */
      public boolean canExistAbstractDbcClassImplements_4005(
            AbstractDbcClass source, DbcInterface target) {
         try {
            if (target == null) {
               return true;
            }
            else {
               Map<String, EClassifier> env = Collections
                     .<String, EClassifier> singletonMap(
                           "oppositeEnd", DbcmodelPackage.eINSTANCE.getAbstractDbcClass()); //$NON-NLS-1$
               Object targetVal = DbCOCLFactory.getExpression(2,
                     DbcmodelPackage.eINSTANCE.getDbcInterface(), env)
                     .evaluate(target,
                           Collections.singletonMap("oppositeEnd", source)); //$NON-NLS-1$
               if (false == targetVal instanceof Boolean
                     || !((Boolean) targetVal).booleanValue()) {
                  return false;
               } // else fall-through
            }
            return true;
         }
         catch (Exception e) {
            DbCDiagramEditorPlugin.getInstance().logError(
                  "Link constraint evaluation error", e); //$NON-NLS-1$
            return false;
         }
      }
   }

}