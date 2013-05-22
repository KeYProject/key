package de.uka.ilkd.key.proof_references.analyst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * Extracts inlined methods.
 * @author Martin Hentschel
 */
public class MethodBodyExpandProofReferencesAnalyst implements IProofReferencesAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services) {
      if (node.getAppliedRuleApp() != null && node.getNodeInfo() != null) {
         NodeInfo info = node.getNodeInfo();
         if (info.getActiveStatement() instanceof MethodBodyStatement) {
            MethodBodyStatement mbs = (MethodBodyStatement)info.getActiveStatement();
            IProgramMethod pm = mbs.getProgramMethod(services);
            DefaultProofReference<IProgramMethod> reference = new DefaultProofReference<IProgramMethod>(IProofReference.INLINE_METHOD, node, pm);
            LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
            result.add(reference);
            return result;
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
}
