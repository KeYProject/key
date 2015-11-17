package org.key_project.sed.key.evaluation.server.random;

import java.io.File;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.input.ToolPageInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.Entry;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.IDataFactory;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.IEntryUpdater;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * The {@link IRandomCompletion} used by the {@link UnderstandingProofAttemptsEvaluation}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsRandomFormOrderComputer extends AbstractRandomCompletion {
   /**
    * The used {@link BalancingEntry} instances for balancing purpose.
    */
   private final Map<String, BalancingEntry> balancingMap = new HashMap<String, BalancingEntry>();

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
      final Map<String, Map<String, IndexData>> existingDataMap = new HashMap<String, Map<String, IndexData>>();
      File[] instructionFiles = FileStorage.listFormFiles(storageLocation, UnderstandingProofAttemptsEvaluation.INSTANCE.getName(), UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
      if (!ArrayUtil.isEmpty(instructionFiles)) {
         for (File file : instructionFiles) {
            try {
               EvaluationInput evaluationInput = EvaluationInputReader.parse(file);
               AbstractFormInput<?> introductionFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME));
               QuestionPageInput backgroundPageInput = (QuestionPageInput)introductionFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
               QuestionInput keyInput = backgroundPageInput.getQuestionInput(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
               RandomFormInput evaluationFormInput = (RandomFormInput)evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
               String permutationKey = null;
               List<Tool> toolOrder = new LinkedList<Tool>();
               if (evaluationFormInput.getPageOrder() != null) {
                  // Analyze page order
                  for (AbstractPageInput<?> pageInput : evaluationFormInput.getPageOrder()) {
                     String pageName = pageInput.getPage().getName();
                     if (ArrayUtil.contains(elements, pageName)) {
                        toolOrder.add(evaluationFormInput.getTool(pageInput));
                        if (permutationKey == null) {
                           permutationKey = pageName;
                        }
                        else {
                           permutationKey += "," + pageName;
                        }
                     }
                  }
                  // Get keyExperience
                  String keyExperience = keyInput.getValue();
                  // Get or create PermutationData
                  Map<String, IndexData> existingMap = existingDataMap.get(keyExperience);
                  if (existingMap == null) {
                     existingMap = new HashMap<String, IndexData>();
                     existingDataMap.put(keyExperience, existingMap);
                  }
                  IndexData data = existingMap.get(permutationKey);
                  if (data == null) {
                     data = new IndexData();
                     existingMap.put(permutationKey, data);
                  }
                  // Update PermutationData
                  if (isToolUsedFirst(toolOrder, UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME, UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME, 4)) {
                     data.increaseKeYCount();
                     if (isCompleted(storageLocation, evaluationInput)) {
                        data.increaseKeYCompletedCount();
                     }
                  }
                  else if (isToolUsedFirst(toolOrder, UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME, UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME, 4)) {
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
      // Get possible experience values
      AbstractForm introductionForm = UnderstandingProofAttemptsEvaluation.INSTANCE.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
      QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
      RadioButtonsQuestion keyQuestion = (RadioButtonsQuestion) backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
      // Create balancing index instances
      for (Choice choice : keyQuestion.getChoices()) {
         final Map<String, IndexData> existingMap = existingDataMap.get(choice.getValue());
         IDataFactory<String, IndexData> dataFactory = new IDataFactory<String, IndexData>() {
            @Override
            public IndexData createData(String[] permutation) {
               if (existingMap != null) {
                  String key = ArrayUtil.toString(permutation, ",");
                  IndexData existingData =  existingMap.remove(key);
                  if (existingData != null) {
                     return existingData;
                  }
                  else {
                     return new IndexData();
                  }
               }
               else {
                  return new IndexData();
               }
            }
         };
         IndexEntryComparator entryComparator = new IndexEntryComparator();
         PermutationIndex<String, IndexData> permutationIndex = new PermutationIndex<String, IndexData>(elements, dataFactory, entryComparator);
         int keyCountTotal = 0;
         int sedCountTotal = 0;
         for (Entry<String, IndexData> indexEntry : permutationIndex.getIndex()) {
            IndexData indexData = indexEntry.getData();
            keyCountTotal += indexData.getKeyCount();
            sedCountTotal += indexData.getSedCount();
         }
         balancingMap.put(choice.getValue(), new BalancingEntry(permutationIndex, keyCountTotal, sedCountTotal));
      }
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
            EvaluationInput evaluationInput = EvaluationInputReader.parse(evaluationFile);
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
    * Returns the used {@link BalancingEntry} for the given KeY experience.
    * @return The used {@link BalancingEntry}.
    */
   public BalancingEntry getBalancingEntry(String keyExperience) {
      return balancingMap.get(keyExperience);
   }

   /**
    * Returns the available {@link BalancingEntry} instances for balancing.
    * @return The available {@link BalancingEntry} instances for balancing.
    */
   public Map<String, BalancingEntry> getBalancingMap() {
      return Collections.unmodifiableMap(balancingMap);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<RandomFormInput> computeRandomValues(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm) {
      try {
         // Get KeY experience
         QuestionPageInput backgroundPage = (QuestionPageInput) currentForm.getPageInput(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         QuestionInput keyExperienceInput = backgroundPage.getQuestionInput(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         BalancingEntry balancingEntry = balancingMap.get(keyExperienceInput.getValue());
         // Update index and compute which order should be returned.
         BalancingEntryUpdater updater = new BalancingEntryUpdater(balancingEntry);
         balancingEntry.getPermutationIndex().updateFirstEntry(updater);
         // Create order
         return computeOrder(evaluationInput, currentForm, updater.getPermutation(), updater.isKeyFirst());
      }
      catch (Exception e) { // In case of an exception return a fixed order as fallback.
         e.printStackTrace();
         return computeFixedOrder(evaluationInput, currentForm, true, false);
      }
   }
   
   /**
    * An {@link IEntryUpdater} used to update a {@link BalancingEntry}.
    * @author Martin Hentschel
    */
   protected static class BalancingEntryUpdater implements IEntryUpdater<String, IndexData> {
      /**
       * The {@link BalancingEntry} to modify.
       */
      private final BalancingEntry balancingEntry;
      
      /**
       * The permutation to use.
       */
      private String[] permutation;

      /**
       * Use KeY first?
       */
      private boolean keyFirst;
      
      /**
       * Constructor.
       * @param balancingEntry The {@link BalancingEntry} to modify.
       */
      public BalancingEntryUpdater(BalancingEntry balancingEntry) {
         this.balancingEntry = balancingEntry;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Entry<String, IndexData> updateEntry(List<Entry<String, IndexData>> list) {
         Entry<String, IndexData> firstEntry = list.get(0);
         permutation = firstEntry.getPermutation();
         IndexData indexData = firstEntry.getData();
         boolean indexUpdateRequired = false;
         // Completed count is ignored for simplicity.
         if (indexData.getKeyCount() < indexData.getSedCount()) {
            keyFirst = true;
            indexUpdateRequired = true;
         }
         else if (indexData.getKeyCount() > indexData.getSedCount()) {
            keyFirst = false;
            indexUpdateRequired = true;
         }
         else {
            keyFirst = balancingEntry.keyCountTotal < balancingEntry.sedCountTotal;
         }
         // Update balancing entry
         if (keyFirst) {
            indexData.increaseKeYCount();
            balancingEntry.keyCountTotal++;
         }
         else {
            indexData.increaseSedCount();
            balancingEntry.sedCountTotal++;
         }
         return indexUpdateRequired ? firstEntry : null;
      }

      /**
       * Returns the permutation to use.
       * @return The permutation to use.
       */
      public String[] getPermutation() {
         return permutation;
      }

      /**
       * Checks if KeY should be used first.
       * @return {@code true} KeY first, {@code false} SED first.
       */
      public boolean isKeyFirst() {
         return keyFirst;
      }
   }
   
   /**
    * Computes a single fixed order.
    * @param evaluationInput The {@link EvaluationInput}.
    * @param currentForm The current {@link AbstractFormInput}.
    * @param keyFirst Use KeY as first tool?
    * @param reverseOrder Reverse fixed order?
    * @return The fixed order.
    */
   public static List<RandomFormInput> computeFixedOrder(EvaluationInput evaluationInput, 
                                                         AbstractFormInput<?> currentForm,
                                                         boolean keyFirst,
                                                         boolean reverseOrder) {
      String[] order = reverseOrder ?
                       new String[] {UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME, UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME} :
                       new String[] {UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME};
      return computeOrder(evaluationInput, currentForm, order, keyFirst);
   }
   
   /**
    * Computes the order.
    * @param evaluationInput The {@link EvaluationInput}.
    * @param currentForm The current {@link AbstractFormInput}.
    * @param proofOrder The order of the proofs.
    * @param keyFirst Use KeY as first tool?
    * @return The computed order.
    */
   @SuppressWarnings("unchecked")
   public static List<RandomFormInput> computeOrder(EvaluationInput evaluationInput, 
                                                    AbstractFormInput<?> currentForm,
                                                    String[] proofOrder,
                                                    boolean keyFirst) {
      // Get needed objects
      RandomForm evaluationForm = ((UnderstandingProofAttemptsEvaluation) evaluationInput.getEvaluation()).getEvaluationForm();
      RandomFormInput evaluationFormInput = (RandomFormInput) evaluationInput.getFormInput(evaluationForm);
      AbstractPageInput<?> evaluationPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.EVALUATION_PAGE_NAME);
      AbstractPageInput<?> jmlPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.JML_PAGE_NAME);
      ToolPageInput tool1Page;
      ToolPageInput tool2Page;
      if (keyFirst) {
         tool1Page = (ToolPageInput) evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME);
         tool2Page = (ToolPageInput) evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME);
      }
      else {
         tool1Page = (ToolPageInput) evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME);
         tool2Page = (ToolPageInput) evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME);
      }
      AbstractPageInput<?> proof1Page = evaluationFormInput.getPageInput(proofOrder[0]);
      AbstractPageInput<?> proof2Page = evaluationFormInput.getPageInput(proofOrder[1]);
      AbstractPageInput<?> proof3Page = evaluationFormInput.getPageInput(proofOrder[2]);
      AbstractPageInput<?> proof4Page = evaluationFormInput.getPageInput(proofOrder[3]);
      AbstractPageInput<?> feedbackPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.FEEDBACK_PAGE);
      AbstractPageInput<?> sendPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SEND_EVALUATION_PAGE_NAME);
      // Set order and tools
      evaluationFormInput.setPageOrder(CollectionUtil.toList(evaluationPage, 
                                                             jmlPage, 
                                                             tool1Page, 
                                                             proof1Page, 
                                                             proof2Page, 
                                                             tool2Page, 
                                                             proof3Page, 
                                                             proof4Page, 
                                                             feedbackPage, 
                                                             sendPage));
      evaluationFormInput.setTool(proof1Page, tool1Page.getPage().getTool());
      evaluationFormInput.setTool(proof2Page, tool1Page.getPage().getTool());
      evaluationFormInput.setTool(proof3Page, tool2Page.getPage().getTool());
      evaluationFormInput.setTool(proof4Page, tool2Page.getPage().getTool());
      return CollectionUtil.toList(evaluationFormInput);
   }
   
   /**
    * The {@link Comparator} used to compare {@link Entry} instances.
    * @author Martin Hentschel
    */
   public static class IndexEntryComparator implements Comparator<Entry<String, IndexData>> {
      /**
       * {@inheritDoc}
       */
      @Override
      public int compare(Entry<String, IndexData> e1, Entry<String, IndexData> e2) {
         IndexData id1 = e1.getData();
         IndexData id2 = e2.getData();
         // Compare balanced state (KeY use equal to SED use), completed count is ignored for simplicity
         boolean o1balanced = id1.getKeyCount() == id1.getSedCount();
         boolean o2balanced = id2.getKeyCount() == id2.getSedCount();
         if (o1balanced && o2balanced) {
            return compareCounts(id1, id2); 
         }
         else if (!o1balanced && o2balanced) {
            return -1;
         }
         else if (o1balanced && !o2balanced) {
            return 1;
         }
         else {
            return compareCounts(id1, id2); 
         }
      }
      
      /**
       * Compares KeY and SED count.
       * @param o1 The first {@link IndexData}.
       * @param o2 The second {@link IndexData}.
       * @return The comparison result.
       */
      protected int compareCounts(IndexData o1, IndexData o2) {
         if (o1.getKeyCount() < o2.getKeyCount() && o1.getSedCount() < o2.getSedCount()) {
            return -1;
         }
         else if (o1.getKeyCount() > o2.getKeyCount() && o1.getSedCount() > o2.getSedCount()) {
            return 1;
         }
         else {
            int o1max = Math.max(o1.getKeyCount(), o1.getSedCount());
            int o2max = Math.max(o2.getKeyCount(), o2.getSedCount());
            if (o1max < o2max) {
               return -1;
            }
            else if (o1max > o2max) {
               return 1;
            }
            else {
               int o1min = Math.min(o1.getKeyCount(), o1.getSedCount());
               int o2min = Math.min(o2.getKeyCount(), o2.getSedCount());
               if (o1min < o2min) {
                  return -1;
               }
               else if (o1min > o2min) {
                  return 1;
               }
               else {
                  return 0;
               }
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
                 ", KeY Completed Count = " + keyCompletedCount +
                 ", SED Count = " + sedCount +
                 ", SED Completed Count = " + sedCompletedCount;
      }
   }
   
   /**
    * Provides all information relevant for balancing.
    * @author Martin Hentschel
    */
   public static class BalancingEntry {
      /**
       * The used {@link PermutationIndex}.
       */
      private final PermutationIndex<String, IndexData> permutationIndex;
      
      /**
       * The total amount of KeY count.
       */
      private int keyCountTotal;
      
      /**
       * The total amount of SED count.
       */
      private int sedCountTotal;

      /**
       * Constructor.
       * @param permutationIndex The used {@link PermutationIndex}.
       * @param keyCountTotal The total amount of KeY count.
       * @param sedCountTotal The total amount of SED count.
       */
      public BalancingEntry(PermutationIndex<String, IndexData> permutationIndex, int keyCountTotal, int sedCountTotal) {
         this.permutationIndex = permutationIndex;
         this.keyCountTotal = keyCountTotal;
         this.sedCountTotal = sedCountTotal;
      }

      /**
       * Returns the used {@link PermutationIndex}.
       * @return The used {@link PermutationIndex}.
       */
      public PermutationIndex<String, IndexData> getPermutationIndex() {
         return permutationIndex;
      }

      /**
       * Returns the total amount of KeY count.
       * @return The total amount of KeY count.
       */
      public int getKeyCountTotal() {
         return keyCountTotal;
      }

      /**
       * Returns the total amount of SED count.
       * @return The total amount of SED count.
       */
      public int getSedCountTotal() {
         return sedCountTotal;
      }
   }
}
