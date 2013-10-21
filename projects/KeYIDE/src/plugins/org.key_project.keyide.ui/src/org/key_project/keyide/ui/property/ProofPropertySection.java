package org.key_project.keyide.ui.property;

import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
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
