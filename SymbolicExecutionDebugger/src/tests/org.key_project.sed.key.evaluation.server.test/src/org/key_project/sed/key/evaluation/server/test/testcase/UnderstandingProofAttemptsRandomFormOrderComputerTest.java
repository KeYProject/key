package org.key_project.sed.key.evaluation.server.test.testcase;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.RadioButtonsQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex;
import org.key_project.sed.key.evaluation.server.index.PermutationIndex.Entry;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.IndexData;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer.IndexDataComparator;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;

/**
 * Tests for {@link UnderstandingProofAttemptsRandomFormOrderComputer}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsRandomFormOrderComputerTest extends TestCase {
   /**
    * Tests {@link IndexDataComparator}.
    */
   @Test
   public void testIndexDataComparator() {
      // Test equal instances
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 0, 0, 0), 0);
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 0, 0, 0), 0);
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 2, 0, 0), 0);
      doComparisionTest(new IndexData(0, 0, 3, 0), new IndexData(0, 0, 3, 0), 0);
      doComparisionTest(new IndexData(0, 0, 0, 4), new IndexData(0, 0, 0, 4), 0);
      // Test random examples
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 0, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 1, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 2, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 2, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // First smaller, because less used
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 1, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(3, 1, 0, 0), 1); // Second smaller, because other tool is missing
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(3, 1, 0, 0), -1); // First smaller, because less used
      // Test different counts systematically
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 0, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(1, 2, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(2, 1, 0, 0), 1); // Bigger as unbalanced
      doComparisionTest(new IndexData(0, 0, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller

      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 1, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(0, 2, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(1, 0, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(2, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(0, 2, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(2, 0, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(0, 2, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 1, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(0, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 0, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(2, 0, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(1, 0, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(0, 0, 0, 0), 1); // Bigger
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(1, 1, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(1, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(1, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller

      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as less unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(1, 2, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as less unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(2, 1, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(1, 2, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(0, 2, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(1, 2, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(2, 0, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(2, 1, 0, 0), -1); // Smaller unbalanced
      doComparisionTest(new IndexData(2, 0, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(0, 0, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(1, 1, 0, 0), -1); // Smaller as unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(1, 2, 0, 0), 0); // Equally unbalanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(2, 1, 0, 0), 0); // Equal
      doComparisionTest(new IndexData(2, 1, 0, 0), new IndexData(2, 2, 0, 0), -1); // Smaller as unbalanced

      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(0, 0, 0, 0), 1); // Bigger
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(0, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(0, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(1, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(1, 1, 0, 0), 1); // Bigger balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(1, 2, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(2, 0, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(2, 1, 0, 0), 1); // Bigger as balanced
      doComparisionTest(new IndexData(2, 2, 0, 0), new IndexData(2, 2, 0, 0), 0); // Equal
   }
   
   /**
    * Compares the given {@link IndexData} using an {@link IndexDataComparator}.
    * The comparison is also performed in reverse order.
    * @param first The first {@link IndexData}.
    * @param second The second {@link IndexData}.
    * @param expectedOutcome The expected outcome.
    */
   protected void doComparisionTest(IndexData first, IndexData second, int expectedOutcome) {
      IndexDataComparator c = new IndexDataComparator();
//      assertEquals(expectedOutcome, c.compare(first, second));
      assertEquals(expectedOutcome * -1, c.compare(second, first)); // Test reverse order
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_NoData() throws Exception {
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      doInitialIndexTest(expectedData);
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleIncompleteKeY() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 0, 0, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleIncompleteSED() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(0, 1, 0, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(false, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleKeY() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 0, 1, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(true, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_SingleSED() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(0, 1, 0, 1));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(false, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE));
   }
   
   /**
    * Tests the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testInitialIndex_Multile() throws Exception {
      Map<String, IndexData> noneData = new HashMap<String, IndexData>();
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(2, 2, 1, 1));
      noneData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME), 
                   new IndexData(2, 2, 1, 1));
      Map<String, IndexData> lessData = new HashMap<String, IndexData>();
      lessData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 0, 0, 0));
      Map<String, IndexData> moreData = new HashMap<String, IndexData>();
      moreData.put(ArrayUtil.toString(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME, 
                                      UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME), 
                   new IndexData(1, 1, 0, 0));
      Map<String, Map<String, IndexData>> expectedData = new HashMap<String, Map<String,IndexData>>();
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, noneData);
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, lessData);
      expectedData.put(UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, moreData);
      doInitialIndexTest(expectedData,
                         new IntroductionFormInputFileCreator(false, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(false, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(false, true, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(false, true, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, false, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, true, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, true, true, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE),
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE),
                         new IntroductionFormInputFileCreator(true, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE),
                         new IntroductionFormInputFileCreator(false, false, false, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE));
   }
   
   /**
    * Performs the test steps to test the initial {@link PermutationIndex} created by {@link UnderstandingProofAttemptsRandomFormOrderComputer#UnderstandingProofAttemptsRandomFormOrderComputer(File)}.
    * @param expectedData The expected {@link IndexData}.
    * @param creators {@link IFormInputFileCreator} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doInitialIndexTest(final Map<String, Map<String, IndexData>> expectedData, 
                                     IFormInputFileCreator... creators) throws Exception {
      assertNotNull(expectedData);
      File storageLocation = IOUtil.createTempDirectory("UnderstandingProofAttemptsRandomFormOrderComputer", "Test");
      try {
         for (IFormInputFileCreator creator : creators) {
            creator.createFormInputFile(storageLocation);
         }
         UnderstandingProofAttemptsRandomFormOrderComputer computer = new UnderstandingProofAttemptsRandomFormOrderComputer(storageLocation);
         // Ensure that all expected indices exist
         AbstractForm introductionForm = UnderstandingProofAttemptsEvaluation.INSTANCE.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
         QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         RadioButtonsQuestion keyQuestion = (RadioButtonsQuestion) backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         assertEquals(keyQuestion.countChoices(), computer.getIndexMap().size());
         for (Choice choice : keyQuestion.getChoices()) {
            assertTrue(computer.getIndexMap().containsKey(choice.getValue()));
            // Ensure right index content
            Map<String, IndexData> expectedIndexData = expectedData.get(choice.getValue());
            for (Entry<String, IndexData> entry : computer.getIndex(choice.getValue()).getIndex()) {
               if (expectedIndexData != null) {
                  String permuationKey = ArrayUtil.toString(entry.getPermutation());
                  IndexData expected = expectedIndexData.get(permuationKey);
                  if (expected != null) {
                     assertIndexData(expected, entry.getData());
                  }
                  else {
                     assertIndexData(new IndexData(), entry.getData());
                  }
               }
               else {
                  assertIndexData(new IndexData(), entry.getData());
               }
            }
         }
      }
      finally {
         IOUtil.delete(storageLocation);
      }
   }
   
   /**
    * Creates form input of the introduction form.
    * @author Martin Hentschel
    */
   protected static class IntroductionFormInputFileCreator implements IFormInputFileCreator {
      /**
       * KeY first?
       */
      private final boolean keyFirst;
      
      /**
       * Reverse order?
       */
      private final boolean reverseOrder;
      
      /**
       * Is the evaluation input completed?
       */
      private final boolean completed;
      
      /**
       * The experience with KeY.
       */
      private final String keyExperience;
      
      /**
       * Constructor.
       * @param keyFirst KeY first?
       * @param reverseOrder Reverse order?
       * @param completed Is the evaluation input completed?
       */
      public IntroductionFormInputFileCreator(boolean keyFirst, boolean reverseOrder, boolean completed, String keyExperience) {
         this.keyFirst = keyFirst;
         this.reverseOrder = reverseOrder;
         this.completed = completed;
         this.keyExperience = keyExperience;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createFormInputFile(File storageLocation) throws Exception {
         EvaluationInput evaluationInput = new EvaluationInput(UnderstandingProofAttemptsEvaluation.INSTANCE);
         AbstractFormInput<?> introductionFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME));
         QuestionPageInput backgroundPageInput = (QuestionPageInput)introductionFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         QuestionInput keyInput = backgroundPageInput.getQuestionInput(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         keyInput.setValue(keyExperience);
         List<RandomFormInput> updatedOrders = UnderstandingProofAttemptsRandomFormOrderComputer.computeFixedOrder(evaluationInput, introductionFormInput, keyFirst, reverseOrder);
         FileStorage.store(storageLocation, introductionFormInput, updatedOrders);
         if (completed) {
            AbstractFormInput<?> evaluationFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
            evaluationInput.setCurrentFormInput(evaluationFormInput);
            FileStorage.store(storageLocation, evaluationFormInput, null);
         }
      }
   }
   
   /**
    * Instances are used to create form input files.
    * @author Martin Hentschel
    */
   protected static interface IFormInputFileCreator {
      /**
       * Creates a form input file.
       * @param storageLocation The storage location to save file at.
       * @throws Exception Occurred Exception.
       */
      public void createFormInputFile(File storageLocation) throws Exception;
   }
   
   /**
    * Ensures that the given {@link IndexData} instances are equal.
    * @param expected The expected {@link IndexData}.
    * @param actual The current {@link IndexData}.
    */
   protected void assertIndexData(IndexData expected, IndexData actual) {
      assertNotSame(expected, actual);
      assertEquals(expected.getKeyCount(), actual.getKeyCount());
      assertEquals(expected.getKeyCompletedCount(), actual.getKeyCompletedCount());
      assertEquals(expected.getSedCount(), actual.getSedCount());
      assertEquals(expected.getSedCompletedCount(), actual.getSedCompletedCount());
   }

   /**
    * Tests {@link UnderstandingProofAttemptsRandomFormOrderComputer#isToolUsedFirst(java.util.List, String, String)}.
    */
   @Test
   public void testIsToolUsedFirst() {
      // Get tools
      Tool key = new Tool("key", null, null);
      Tool sed = new Tool("sed", null, null);
      Tool invalid = new Tool("invalidTool", null, null);
      // Perform tests
      assertTrue(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed, sed), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(sed, sed, key, key), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, sed, key, sed), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(invalid, key, sed, sed), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, invalid, sed, sed), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, invalid, sed), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed, invalid), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed), key.getName(), sed.getName()));
      assertFalse(UnderstandingProofAttemptsRandomFormOrderComputer.isToolUsedFirst(CollectionUtil.toList(key, key, sed, sed, sed), key.getName(), sed.getName()));
   }
}
