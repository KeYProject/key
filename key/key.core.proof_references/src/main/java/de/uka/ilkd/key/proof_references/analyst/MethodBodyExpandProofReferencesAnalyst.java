// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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