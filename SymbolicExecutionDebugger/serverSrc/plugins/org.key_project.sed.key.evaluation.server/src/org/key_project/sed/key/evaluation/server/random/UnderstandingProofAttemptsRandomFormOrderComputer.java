package org.key_project.sed.key.evaluation.server.random;

import java.io.File;
import java.io.FileInputStream;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.IDataFactory;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * The {@link IRandomCompletion} used by the {@link UnderstandingProofAttemptsEvaluation}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsRandomFormOrderComputer implements IRandomCompletion {
   /**
    * The used {@link PermutationIndex}.
    */
   private PermutationIndex<String, IndexData> index;

   /**
    * Constructor.
    * @param storageLocation The storage location providing existing evaluation inputs.
    */
   public UnderstandingProofAttemptsRandomFormOrderComputer(File storageLocation) {
      String[] elements = {UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                           UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                           UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME, 
                           UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME};
      // Analyze existing documents
      final Map<String, IndexData> existingDataMap = new HashMap<String, IndexData>();
      File[] instructionFiles = FileStorage.listFormFiles(storageLocation, UnderstandingProofAttemptsEvaluation.INSTANCE.getName(), UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
      if (!ArrayUtil.isEmpty(instructionFiles)) {
         for (File file : instructionFiles) {
            try {
               EvaluationInput evaluationInput = EvaluationInputReader.parse(new FileInputStream(file));
               RandomFormInput formInput = (RandomFormInput)evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
               String permutationKeY = null;
               List<Tool> toolOrder = new LinkedList<Tool>();
               if (formInput.getPageOrder() != null) {
                  // Analyze page order
                  for (AbstractPageInput<?> pageInput : formInput.getPageOrder()) {
                     String pageName = pageInput.getPage().getName();
                     if (ArrayUtil.contains(elements, pageName)) {
                        toolOrder.add(formInput.getTool(pageInput));
                        if (permutationKeY == null) {
                           permutationKeY = pageName;
                        }
                        else {
                           permutationKeY += "," + pageName;
                        }
                     }
                  }
                  // Get or create PermutationData
                  IndexData data = existingDataMap.get(permutationKeY);
                  if (data == null) {
                     data = new IndexData();
                     existingDataMap.put(permutationKeY, data);
                  }
                  // Update PermutationData
                  if (isToolUsedFirst(toolOrder, UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME, UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME)) {
                     data.increaseKeYCount();
                     if (isCompleted(storageLocation, evaluationInput)) {
                        data.increaseKeYCompletedCount();
                     }
                  }
                  else if (isToolUsedFirst(toolOrder, UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME, UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME)) {
                     data.increaseSedCount();
                     if (isCompleted(storageLocation, evaluationInput)) {
                        data.increaseSedCompletedCount();
                     }
                  }
               }
            }
            catch (Exception e) {
               e.printStackTrace();
            }
         }
      }
      // Create index
      IDataFactory<String, IndexData> dataFactory = new IDataFactory<String, IndexData>() {
         @Override
         public IndexData createData(String[] permutation) {
            String key = ArrayUtil.toString(permutation, ",");
            IndexData existingData =  existingDataMap.remove(key);
            if (existingData != null) {
               return existingData;
            }
            else {
               return new IndexData();
            }
         }
      };
      IndexDataComparator dataComparator = new IndexDataComparator();
      index = new PermutationIndex<String, IndexData>(elements, dataFactory, dataComparator);
   }

   /**
    * Checks if the given {@link EvaluationInput} is completed meaning
    * that the evaluation form is also available.
    * @param storageLocation The storage location.
    * @param introductionInput The {@link EvaluationInput} of the introduction form.
    * @return {@code true} is completed, {@code false} is not completed.
    */
   protected boolean isCompleted(File storageLocation, EvaluationInput introductionInput) {
      try {
         File evaluationFile = FileStorage.getFile(storageLocation, UnderstandingProofAttemptsEvaluation.INSTANCE.getName(), UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME, introductionInput.getUUID());
         if (evaluationFile != null) {
            EvaluationInput evaluationInput = EvaluationInputReader.parse(new FileInputStream(evaluationFile));
            return ObjectUtil.equals(evaluationInput.getUUID(), introductionInput.getUUID());
         }
         else {
            return false;
         }
      }
      catch (Exception e) {
         return false; // Treat unparsable files as not completed.
      }
   }

   /**
    * Returns the used {@link PermutationIndex}.
    * @return The used {@link PermutationIndex}.
    */
   public PermutationIndex<String, IndexData> getIndex() {
      return index;
   }

   /**
    * Checks if the {@link Tool} order uses the first tool first and then the second tool.
    * @param toolOrder The {@link Tool} order to check.
    * @param firstToolName The name of the first tool.
    * @param secondToolName The name of the second tool.
    * @return {@code true} first tool is used first, {@code false} first tool is not used first or tool order is invalid.
    */
   public static boolean isToolUsedFirst(List<Tool> toolOrder, String firstToolName, String secondToolName) {
      if (toolOrder.size() == 4) {
         boolean keyFirst = true;
         Iterator<Tool> iter = toolOrder.iterator();
         int i = 0;
         while (keyFirst && iter.hasNext()) {
            Tool next = iter.next();
            if (i < 2) {
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

   /**
    * {@inheritDoc}
    */
   @Override
   public List<RandomFormInput> computeRandomValues(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm) {
      // TODO: Compute a real random order!
      return computeFixedOrder(evaluationInput, currentForm, true, false);
   }
   
   @SuppressWarnings("unchecked")
   public static List<RandomFormInput> computeFixedOrder(EvaluationInput evaluationInput, 
                                                         AbstractFormInput<?> currentForm,
                                                         boolean keyFirst,
                                                         boolean reverseOrder) {
      // Get needed objects
      RandomForm evaluationForm = ((UnderstandingProofAttemptsEvaluation) evaluationInput.getEvaluation()).getEvaluationForm();
      RandomFormInput evaluationFormInput = (RandomFormInput) evaluationInput.getFormInput(evaluationForm);
      AbstractPageInput<?> evaluationPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.EVALUATION_PAGE_NAME);
      AbstractPageInput<?> jmlPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.JML_PAGE_NAME);
      AbstractPageInput<?> keyPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME);
      AbstractPageInput<?> sedPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME);
      AbstractPageInput<?> proof1Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME);
      AbstractPageInput<?> proof2Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME);
      AbstractPageInput<?> proof3Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME);
      AbstractPageInput<?> proof4Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME);
      AbstractPageInput<?> feedbackPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.FEEDBACK_PAGE);
      AbstractPageInput<?> sendPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SEND_EVALUATION_PAGE_NAME);
      // Set order and tools
      if (reverseOrder) {
         evaluationFormInput.setPageOrder(CollectionUtil.toList(evaluationPage, jmlPage, keyPage, proof3Page, proof4Page, sedPage, proof1Page, proof2Page, feedbackPage, sendPage));
      }
      else {
         evaluationFormInput.setPageOrder(CollectionUtil.toList(evaluationPage, jmlPage, keyPage, proof2Page, proof1Page, sedPage, proof4Page, proof3Page, feedbackPage, sendPage));
      }
      Tool keyTool = evaluationForm.getEvaluation().getTool(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME);
      Tool sedTool = evaluationForm.getEvaluation().getTool(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME);
      if (keyFirst) {
         evaluationFormInput.setTool(proof2Page, keyTool);
         evaluationFormInput.setTool(proof1Page, keyTool);
         evaluationFormInput.setTool(proof4Page, sedTool);
         evaluationFormInput.setTool(proof3Page, sedTool);
      }
      else {
         evaluationFormInput.setTool(proof2Page, sedTool);
         evaluationFormInput.setTool(proof1Page, sedTool);
         evaluationFormInput.setTool(proof4Page, keyTool);
         evaluationFormInput.setTool(proof3Page, keyTool);
      }
      return CollectionUtil.toList(evaluationFormInput);
   }
   
   /**
    * The {@link Comparator} used to compare {@link IndexData} instances.
    * @author Martin Hentschel
    */
   public static class IndexDataComparator implements Comparator<IndexData> {
      /**
       * {@inheritDoc}
       */
      @Override
      public int compare(IndexData o1, IndexData o2) {
         // Compare first completed count
         if (o1.getKeyCompletedCount() < o2.getKeyCompletedCount() || o1.getSedCompletedCount() < o2.getSedCompletedCount()) {
            return -1;
         }
         else if (o1.getKeyCompletedCount() > o2.getKeyCompletedCount() || o1.getSedCompletedCount() > o2.getSedCompletedCount()) {
            return 1;
         }
         else {
            // Compare second first use count
            if (o1.getKeyCount() < o2.getKeyCount() || o1.getSedCount() < o2.getSedCount()) {
               return -1;
            }
            else if (o1.getKeyCount() > o2.getKeyCount() || o1.getSedCount() > o2.getSedCount()) {
               return 1;
            }
            else {
               return 0;
            }
         }
      }
   }

   /**
    * The data stored in the used {@link PermutationIndex}.
    * @author Martin Hentschel
    */
   public static class IndexData {
      /**
       * Counts how often KeY was used first.
       */
      private int keyCount;

      /**
       * Counts how often SED was used first.
       */
      private int sedCount;

      /**
       * Counts how often KeY is completed.
       */
      private int keyCompletedCount;

      /**
       * Counts how often SED is completed.
       */
      private int sedCompletedCount;
      
      /**
       * Constructor.
       */
      public IndexData() {
         this(0, 0, 0, 0);
      }
      
      /**
       * Constructor.
       * @param keyCount The KeY used first counter.
       * @param sedCount The SED used first counter.
       * @param keyCompletedCount The KeY completed counter.
       * @param sedCompletedCount The SED completed counter.
       */
      public IndexData(int keyCount, int sedCount, int keyCompletedCount, int sedCompletedCount) {
         this.keyCount = keyCount;
         this.sedCount = sedCount;
         this.keyCompletedCount = keyCompletedCount;
         this.sedCompletedCount = sedCompletedCount;
      }

      /**
       * Increases the KeY used first counter by {@code 1}.
       */
      protected void increaseKeYCount() {
         keyCount++;
      }
      
      /**
       * Increases the SED used first counter by {@code 1}.
       */
      protected void increaseSedCount() {
         sedCount++;
      }
      
      /**
       * Increases the KeY completed counter by {@code 1}.
       */
      protected void increaseKeYCompletedCount() {
         keyCompletedCount++;
      }
      
      /**
       * Increases the SED completed counter by {@code 1}.
       */
      protected void increaseSedCompletedCount() {
         sedCompletedCount++;
      }

      /**
       * Returns the KeY used first counter.
       * @return The KeY used first counter.
       */
      public int getKeyCount() {
         return keyCount;
      }

      /**
       * Returns the SED used first counter.
       * @return The SED used first counter.
       */
      public int getSedCount() {
         return sedCount;
      }

      /**
       * Returns the KeY completed counter.
       * @return The KeY completed counter.
       */
      public int getKeyCompletedCount() {
         return keyCompletedCount;
      }

      /**
       * Returns the SED completed counter.
       * @return The SED completed counter.
       */
      public int getSedCompletedCount() {
         return sedCompletedCount;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return "KeY Count = " + keyCount + 
                 ", KeY Completed Count" + keyCompletedCount +
                 ", SED Count" + sedCount +
                 ", SED Completed Count" + sedCompletedCount;
      }
   }
}
