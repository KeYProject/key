package org.key_project.sed.key.evaluation.server.test.testcase;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.Test;
import org.key_project.sed.key.evaluation.io.SendThread;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.model.test.testcase.AbstractEvaluationModelTest;
import org.key_project.sed.key.evaluation.server.implementation.SEDServer;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link SEDServer}.
 * @author Martin Hentschel
 */
public class SEDServerTest extends AbstractEvaluationModelTest {
   /**
    * The port used during tests.
    */
   private static final int TEST_PORT = 1234;
   
   /**
    * Tests the {@link SEDServer} pinging.
    */
   @Test
   public void testPing() throws Exception {
      File storageLocation = IOUtil.createTempDirectory("SEDServer", "Test");
      ServerThread serverThread = null;
      try {
         // Start server
         serverThread = new ServerThread(storageLocation);
         serverThread.start();
         // Ensure that no storage content exists yet
         assertEquals(0, storageLocation.listFiles().length);
         // Ping server
         long time = SendThread.ping("localhost", TEST_PORT);
         assertTrue(time >= 0);
         serverThread.assertStorageContent();
         // Simulate valid client requests
         serverThread.assertStorageContent();
         sendUnderstandingProofAttemptsIntroductionForm(storageLocation, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE);
         serverThread.assertStorageContent();
      }
      finally {
         IOUtil.delete(storageLocation);
         if (serverThread != null) {
            serverThread.stopServer();
         }
      }
   }
   
   /**
    * Tests the {@link SEDServer} with incoming invalid content.
    */
   @Test
   public void testInvalidContent() throws Exception {
      File storageLocation = IOUtil.createTempDirectory("SEDServer", "Test");
      ServerThread serverThread = null;
      try {
         // Start server
         serverThread = new ServerThread(storageLocation);
         serverThread.start();
         // Ensure that no storage content exists yet
         assertEquals(0, storageLocation.listFiles().length);
         // Simulate invalid client request
         serverThread.assertStorageContent();
         try {
            sendXml("Invalid XML content!");
            fail("Exception expected.");
         }
         catch (Exception e) {
            assertNotNull(e.getMessage());
         }
         serverThread.assertStorageContent();
         // Simulate valid client requests
         serverThread.assertStorageContent();
         sendUnderstandingProofAttemptsIntroductionForm(storageLocation, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE);
         serverThread.assertStorageContent();
      }
      finally {
         IOUtil.delete(storageLocation);
         if (serverThread != null) {
            serverThread.stopServer();
         }
      }
   }
   
   /**
    * Tests the {@link SEDServer} with incoming {@link UnderstandingProofAttemptsEvaluation} requests.
    */
   @Test
   public void testUnderstandingProofAttemptsRequests() throws Exception {
      File storageLocation = IOUtil.createTempDirectory("SEDServer", "Test");
      ServerThread serverThread = null;
      try {
         // Start server
         serverThread = new ServerThread(storageLocation);
         serverThread.start();
         // Ensure that no storage content exists yet
         assertEquals(0, storageLocation.listFiles().length);
         // Simulate client requests
         for (int i = 0; i < 10; i++) {
            String keyExperience;
            if (i % 3 == 0) {
               keyExperience = UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE;
            }
            else if (i % 3 == 0) {
               keyExperience = UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE;
            }
            else {
               keyExperience = UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE;
            }
            serverThread.assertStorageContent();
            EvaluationInput input = sendUnderstandingProofAttemptsIntroductionForm(storageLocation, keyExperience);
            serverThread.assertStorageContent();
            sendUnderstandingProofAttemptsEvaluationForm(storageLocation, input);
            serverThread.assertStorageContent();
         }
      }
      finally {
         IOUtil.delete(storageLocation);
         if (serverThread != null) {
            serverThread.stopServer();
         }
      }
   }

   /**
    * Sends the introduction form to the server.
    * @param storageLocation The file storage of the server.
    * @param keyExperience The KeY experience.
    * @return The created {@link EvaluationInput}.
    * @throws Exception Occurred Exception.
    */
   protected EvaluationInput sendUnderstandingProofAttemptsIntroductionForm(File storageLocation, String keyExperience) throws Exception {
      EvaluationInput evaluationInput = new EvaluationInput(UnderstandingProofAttemptsEvaluation.INSTANCE);
      AbstractFormInput<?> introductionFormInput = evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME));
      QuestionPageInput backgroundPageInput = (QuestionPageInput) introductionFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
      QuestionInput keyQuestion = backgroundPageInput.getQuestionInput(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
      keyQuestion.setValue(keyExperience);
      RandomFormInput evaluationFormInput = (RandomFormInput)evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
      assertNull(evaluationFormInput.getPageOrder());
      for (AbstractPageInput<?> pageInput : evaluationFormInput.getPageInputs()) {
         assertNull(evaluationFormInput.getTool(pageInput));
      }
      // Test initial values
      assertNull(evaluationInput.getUUID());
      // Send evaluation input
      EvaluationInput answerEvaluationInput = sendFormAnswer(introductionFormInput);
      RandomFormInput answerFormInput = (RandomFormInput)answerEvaluationInput.getFormInput(answerEvaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
      // Update evaluation input
      SendThread.updateUUID(evaluationInput, answerEvaluationInput);
      SendThread.updatePageOrder(evaluationInput, answerEvaluationInput);
      // Ensure right values
      assertNotNull(evaluationInput.getUUID());
      assertEquals(answerEvaluationInput.getUUID(), evaluationInput.getUUID());
      assertNotNull(evaluationFormInput.getPageOrder());
      assertPageInputs(evaluationFormInput.getPageOrder(), answerFormInput.getPageOrder());
      assertTools(evaluationFormInput, answerFormInput);
      // Ensure that answer was saved on server
      File savedFile = FileStorage.getFile(storageLocation, evaluationInput.getEvaluation().getName(), introductionFormInput.getForm().getName(), answerEvaluationInput.getUUID());
      assertNotNull(savedFile);
      assertTrue(savedFile.isFile());
      EvaluationInput readEvaluationInput = EvaluationInputReader.parse(new FileInputStream(savedFile));
      assertEvaluationInput(evaluationInput, readEvaluationInput, true, true, ValueComparison.SET);
      return evaluationInput;
   }
   
   /**
    * Sends the evaluation form to the server.
    * @param storageLocation The file storage of the server.
    * @param evaluationInput The {@link EvaluationInput} to send.
    * @throws Exception Occurred Exception.
    */
   protected void sendUnderstandingProofAttemptsEvaluationForm(File storageLocation, EvaluationInput evaluationInput) throws Exception {
      String oldUUID = evaluationInput.getUUID();
      assertNotNull(oldUUID);
      RandomFormInput evaluationFormInput = (RandomFormInput)evaluationInput.getFormInput(evaluationInput.getEvaluation().getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME));
      evaluationInput.setCurrentFormInput(evaluationFormInput);
      // Send evaluation input
      EvaluationInput answerEvaluationInput = sendFormAnswer(evaluationFormInput);
      // Update evaluation input
      SendThread.updateUUID(evaluationInput, answerEvaluationInput);
      SendThread.updatePageOrder(evaluationInput, answerEvaluationInput);
      // Ensure right values
      assertEquals(oldUUID, evaluationInput.getUUID());
      for (AbstractFormInput<?> formInput : answerEvaluationInput.getFormInputs()) {
         if (formInput instanceof RandomFormInput) {
            assertNull(((RandomFormInput) formInput).getPageOrder());
         }
      }
      // Ensure that answer was saved on server
      File savedFile = FileStorage.getFile(storageLocation, evaluationInput.getEvaluation().getName(), evaluationFormInput.getForm().getName(), answerEvaluationInput.getUUID());
      assertNotNull(savedFile);
      assertTrue(savedFile.isFile());
      EvaluationInput readEvaluationInput = EvaluationInputReader.parse(new FileInputStream(savedFile));
      assertEvaluationInput(answerEvaluationInput, readEvaluationInput, true, true, ValueComparison.SET);
   }
   
   /**
    * Sends the given {@link AbstractFormInput} to the server.
    * @param input The {@link AbstractFormInput} to send.
    * @return The received {@link EvaluationInput} as answer.
    * @throws Exception Occurred Exception.
    */
   protected EvaluationInput sendFormAnswer(AbstractFormInput<?> input) throws Exception {
      assertNotNull(input);
      String xml = EvaluationInputWriter.toFormAnswerXML(input);
      return sendXml(xml);
   }
   
   /**
    * Sends the given XML file to the server.
    * @param message The XML file.
    * @return The read {@link EvaluationInput}.
    * @throws Exception Occurred Exception.
    */
   protected EvaluationInput sendXml(String message) throws Exception {
      SendThread thread = new SendThread(message, "localhost", TEST_PORT);
      thread.run();
      if (thread.getException() != null) {
         throw thread.getException();
      }
      assertNotNull(thread.getAnswer());
      assertNotNull(thread.getAnswerInput());
      assertEvaluationInput(EvaluationInputReader.parse(thread.getAnswer()), thread.getAnswerInput(), true, true, ValueComparison.EQUAL);
      return thread.getAnswerInput();
   }
   
   /**
    * A {@link Thread} in which a {@link SEDServer} is executed.
    * @author Martin Hentschel
    */
   public static class ServerThread extends Thread {
      /**
       * The executed {@link SEDServer}.
       */
      private final SEDServer server;
      
      /**
       * The storage location.
       */
      private final File storageLocation;
      
      /**
       * Collects the content in the storage location.
       */
      private final Map<File, String> storageContentMap = new HashMap<File, String>();
      
      /**
       * Constructor.
       * @param storageLocation The storage location to use.
       */
      public ServerThread(File storageLocation) {
         this.storageLocation = storageLocation;
         server = new SEDServer(storageLocation, TEST_PORT);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run() {
         try {
            server.start();
         }
         catch (IOException e) {
            e.printStackTrace();
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public synchronized void start() {
         super.start();
         while (!isSeverRunning()) {
            TestUtilsUtil.sleep(10);
         }
         assertTrue(isSeverRunning());
      }

      /**
       * Stops the {@link Thread} and the {@link SEDServer}.
       */
      public void stopServer() {
         server.stop();
         while (isAlive()) {
            TestUtilsUtil.sleep(10);
         }
         assertFalse(isSeverRunning());
         assertFalse(isAlive());
      }
      
      /**
       * Checks if the {@link SEDServer} is running.
       * @return {@code true} running, {@code false} not running.
       */
      public boolean isSeverRunning() {
         return server != null && server.isRunning();
      }
      
      /**
       * Ensures that once a {@link File} in the storage location is created
       * its content never changes.
       * @throws Exception Occurred Exception.
       */
      public void assertStorageContent() throws Exception {
         assertFile(storageLocation);
      }
      
      /**
       * Ensures recursively that once a {@link File} is created its content
       * never changes.
       * @param file The current {@link File} to check.
       * @throws Exception Occurred Exception.
       */
      protected void assertFile(File file) throws Exception {
         if (file.isFile()) {
            String currentContent = IOUtil.readFrom(file);
            String expectedContent = storageContentMap.get(file);
            if (expectedContent != null) {
               assertEquals(expectedContent, currentContent);
            }
            else {
               storageContentMap.put(file, currentContent);
            }
         }
         else {
            File[] children = file.listFiles();
            if (children != null) {
               for (File child : children) {
                  assertFile(child);
               }
            }
         }
      }
   }
}
