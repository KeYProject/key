package de.hentschel.visualdbc.dbcmodel.diagram.edit.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.emf.type.core.requests.CreateElementRequest;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.commands.DbCAxiomContractCreateCommand;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;

/**
 * @generated
 */
public class DbcAxiomDbcAxiomCompartmentItemSemanticEditPolicy extends
      DbCBaseItemSemanticEditPolicy {

   /**
    * @generated
    */
   public DbcAxiomDbcAxiomCompartmentItemSemanticEditPolicy() {
      super(DbCElementTypes.DbcAxiom_3036);
   }

   /**
    * @generated
    */
   protected Command getCreateCommand(CreateElementRequest req) {
      if (DbCElementTypes.DbCAxiomContract_3037 == req.getElementType()) {
         return getGEFWrapper(new DbCAxiomContractCreateCommand(req));
      }
      return super.getCreateCommand(req);
   }

}
