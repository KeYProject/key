package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.util.Collection;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.BalancingEntry;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.IndexData;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.ArrayUtil;

/**
 * Appends the balancing distribution section
 * @author Martin Hentschel
 */
public class HTMLUnderstandingProofAttemptsBalancingSectionAppender implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      sb.append("<h1><a name=\"choices\">Balancing Distribution</a></h1>");
      UnderstandingProofAttemptsRandomFormOrderComputer computer = new UnderstandingProofAttemptsRandomFormOrderComputer(storageLocation);
      sb.append("<table border=\"0\" cellpadding=\"0\" cellspacing=\"0\">");
      sb.append("<tr>");
      for (Entry<String, BalancingEntry> entry : computer.getBalancingMap().entrySet()) {
         sb.append("<td>");
         sb.append("<table border=\"1\">");
         // Append header
         sb.append("<tr>");
         sb.append("<td colspan=\"5\" align=\"center\"><b>");
         sb.append(entry.getKey());
         sb.append(" (KeY = ");
         sb.append(entry.getValue().getKeyCountTotal());
         sb.append(", SED = ");
         sb.append(entry.getValue().getSedCountTotal());
         sb.append(")</b></td>");
         sb.append("<tr>");
         sb.append("<td><b>Permutation</b></td>");
         sb.append("<td><b>KeY Count</b></td>");
         sb.append("<td><b>KeY Completed Count</b></td>");
         sb.append("<td><b>SED Count</b></td>");
         sb.append("<td><b>SED Completed Count</b></td>");
         sb.append("</tr>");
         // Append index
         PermutationIndex<String, IndexData> index = entry.getValue().getPermutationIndex();
         for (org.key_project.sed.key.evaluation.server.index.PermutationIndex.Entry<String, IndexData> indexEntry : index.getIndex()) {
            sb.append("<tr>");
            sb.append("<td>");
            sb.append(ArrayUtil.toString(indexEntry.getPermutation()));
            sb.append("</td>");
            sb.append("<td>");
            sb.append(indexEntry.getData().getKeyCount());
            sb.append("</td>");
            sb.append("<td>");
            sb.append(indexEntry.getData().getKeyCompletedCount());
            sb.append("</td>");
            sb.append("<td>");
            sb.append(indexEntry.getData().getSedCount());
            sb.append("</td>");
            sb.append("<td>");
            sb.append(indexEntry.getData().getSedCompletedCount());
            sb.append("</td>");
            sb.append("</tr>");
         }
         sb.append("</tr>");
         sb.append("</table>");
         sb.append("</td>");
         sb.append("<td>&nbsp;&nbsp;</td>");
      }
      sb.append("</tr>");
      sb.append("</table>");
      return null;
   }
}
