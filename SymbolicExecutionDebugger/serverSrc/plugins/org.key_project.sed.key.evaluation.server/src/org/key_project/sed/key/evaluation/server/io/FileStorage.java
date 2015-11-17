package org.key_project.sed.key.evaluation.server.io;

import java.io.File;
import java.io.FileFilter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.List;
import java.util.UUID;

import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.server.Activator;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Provides functionality to store evaluation results.
 * @author Martin Hentschel
 */
public class FileStorage {
   /**
    * The name of the sub directory containing evaluation results.
    */
   private static final String EVALUTION_SUB_DIR = "evaluations";
   
   /**
    * The location at which evaluation results will be stored.
    */
   public static final File FORM_STORAGE_LOCATION;
   
   /**
    * The file extension used to store {@link AbstractFormInput}s as XML file.
    */
   public static final String FORM_FILE_EXTENSION = "xml";
   
   /**
    * The file extension used to store {@link AbstractFormInput}s as XML file.
    */
   public static final String FORM_FILE_EXTENSION_WITH_DOT = "." + FORM_FILE_EXTENSION;
   
   /**
    * Class constructor.
    */
   static {
      if (Activator.getDefault() != null) {
         String statePath = Activator.getDefault().getStateLocation().toString();
         FORM_STORAGE_LOCATION = new File(new File(statePath).getAbsoluteFile(), EVALUTION_SUB_DIR);
      }
      else {
         FORM_STORAGE_LOCATION = new File(new File(".").getAbsoluteFile(), EVALUTION_SUB_DIR);
      }
      FORM_STORAGE_LOCATION.mkdirs();
   }
   
   /**
    * Forbid instances.
    */
   private FileStorage() {
   }

   /**
    * Stores the given {@link AbstractFormInput}.
    * @param storageLocation The storage location.
    * @param formInput The {@link AbstractFormInput} to store.
    * @param updatedOrders The {@link RandomFormInput}s with updated orders.
    * @return The new {@link UUID} under which the form input has been stored or {@code null} if {@link AbstractFormInput#getUUID()} was already defined.
    * @throws IOException Occurred Exception.
    */
   public static String store(File storageLocation, AbstractFormInput<?> formInput, List<RandomFormInput> updatedOrders) throws IOException {
      File evaluationFolder = new File(storageLocation, formInput.getForm().getEvaluation().getName());
      File formFolder = new File(evaluationFolder, formInput.getForm().getName());
      formFolder.mkdirs();
      formInput.getEvaluationInput().setTimestamp(System.currentTimeMillis());
      if (StringUtil.isTrimmedEmpty(formInput.getEvaluationInput().getUUID())) {
         // Create a new UUID.
         String uuid = UUID.randomUUID().toString();
         File file = new File(formFolder, uuid + FORM_FILE_EXTENSION_WITH_DOT);
         synchronized (FileStorage.class) {
            while (file.exists()) {
               uuid = UUID.randomUUID().toString();
               file = new File(formFolder, uuid + FORM_FILE_EXTENSION_WITH_DOT);
            }
            formInput.getEvaluationInput().setUUID(uuid);
            IOUtil.writeTo(new FileOutputStream(file), EvaluationInputWriter.toFormAnswerXML(formInput, updatedOrders));
         }
         return uuid;
      }
      else {
         // Store form with given UUID
         String uuid = formInput.getEvaluationInput().getUUID();
         String currentFileName = uuid;
         String xml = EvaluationInputWriter.toFormAnswerXML(formInput, updatedOrders);
         File file = new File(formFolder, currentFileName + FORM_FILE_EXTENSION_WITH_DOT);
         int counter = 2;
         synchronized (FileStorage.class) {
            while (file.exists()) {
               currentFileName = uuid + "_" + counter;
               file = new File(formFolder, currentFileName + FORM_FILE_EXTENSION_WITH_DOT);
               counter++;
            }
            IOUtil.writeTo(new FileOutputStream(file), xml);
         }
         return null;
      }
   }
   
   /**
    * Lists all {@link File}s providing form inputs.
    * @param storageLocation The storage location.
    * @param evaluation The name of the evaluation.
    * @param form The name of the form.
    * @return The available {@link File}s.
    */
   public static File[] listFormFiles(File storageLocation, String evaluation, String form) {
      File evaluationFolder = new File(storageLocation, evaluation);
      File formFolder = new File(evaluationFolder, form);
      if (formFolder.exists()) {
         return formFolder.listFiles(new FileFilter() {
            @Override
            public boolean accept(File pathname) {
               return FORM_FILE_EXTENSION.equals(IOUtil.getFileExtension(pathname));
            }
         });
      }
      else {
         return null;
      }
   }

   /**
    * Returns the {@link File} providing the specified form input.
    * @param storageLocation The storage location.
    * @param evaluation The name of the evaluation.
    * @param form The name of the form.
    * @param uuid The UUID of the answer.
    * @return The {@link File} or {@code null} if not available.
    */
   public static File getFile(File storageLocation, String evaluation, String form, String uuid) {
      File evaluationFolder = new File(storageLocation, evaluation);
      File formFolder = new File(evaluationFolder, form);
      File formFile = new File(formFolder, uuid + FORM_FILE_EXTENSION_WITH_DOT);
      return formFile.isFile() ? formFile : null;
   }
}
