package org.key_project.sed.key.evaluation.server.random;

import java.util.Iterator;
import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.Tool;

/**
 * Provides the basic functionality of {@link IRandomCompletion}s.
 * @author Martin Hentschel
 */
public abstract class AbstractRandomCompletion implements IRandomCompletion {
   /**
    * Checks if the {@link Tool} order uses the first tool first and then the second tool.
    * @param toolOrder The {@link Tool} order to check.
    * @param firstToolName The name of the first tool.
    * @param secondToolName The name of the second tool.
    * @param numOfExamples The number of examples.
    * @return {@code true} first tool is used first, {@code false} first tool is not used first or tool order is invalid.
    */
   public static boolean isToolUsedFirst(List<Tool> toolOrder, String firstToolName, String secondToolName, int numOfExamples) {
      if (toolOrder.size() == numOfExamples) {
         boolean keyFirst = true;
         Iterator<Tool> iter = toolOrder.iterator();
         int i = 0;
         while (keyFirst && iter.hasNext()) {
            Tool next = iter.next();
            if (i < (numOfExamples / 2)) {
               if (next == null || !firstToolName.equals(next.getName())) {
                  keyFirst = false;
               }
            }
            else {
               if (next == null || !secondToolName.equals(next.getName())) {
                  keyFirst = false;
               }
            }
            i++;
         }
         return keyFirst;
      }
      else {
         return false;
      }
   }
}
