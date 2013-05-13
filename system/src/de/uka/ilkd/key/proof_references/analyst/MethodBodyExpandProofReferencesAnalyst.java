package de.uka.ilkd.key.proof_references.analyst;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * Extracts {@link MethodBodyExpandProofReference}s.
 * @author Martin Hentschel
 */
public class MethodBodyExpandProofReferencesAnalyst implements IProofReferencesAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<IProofReference<?>> computeReferences(Node node, Services services) {
      if (node.getNodeInfo() != null) {
         NodeInfo info = node.getNodeInfo();
         if (info.getActiveStatement() instanceof MethodBodyStatement) {
            MethodBodyStatement mbs = (MethodBodyStatement)info.getActiveStatement();
            IProgramMethod pm = mbs.getProgramMethod(services);
            DefaultProofReference<IProgramMethod> reference = new DefaultProofReference<IProgramMethod>(ProofReferenceUtil.INLINE_METHOD, node, pm);
            return ImmutableSLList.<IProofReference<?>>nil().append(reference);
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
