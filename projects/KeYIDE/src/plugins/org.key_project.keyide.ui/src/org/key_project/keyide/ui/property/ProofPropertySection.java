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

package org.key_project.keyide.ui.property;

import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Proof.Statistics;
import de.uka.ilkd.key.util.Pair;

/**
 * Shows the {@link Proof} {@link Statistics}.
 * @author Martin Hentschel
 */
public class ProofPropertySection extends AbstractKeyValueNodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void updateShownContent(KeYMediator mediator, Node node) {
      // Reset old values
      resetTexts();
      // Show new values
      if (node != null) {
         Proof proof = node.proof();
         List<Pair<String, String>> summary = proof.statistics().getSummary();
         for (Pair<String, String> pair : summary) {
            showText(pair.first, pair.second, null);
         }
      }
   }
}