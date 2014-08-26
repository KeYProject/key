package org.key_project.key4eclipse.resources.log;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.NumberUtil;
import org.key_project.util.java.StringUtil;

/**
 * A log manager is responsible to write and read {@link LogRecord}s
 * into the log file of a KeY project which is a file in the proof folder
 * of name {@link #LOG_FILE_NAME}.
 * <p>
 * The log file is a CSV file in which each line represents a {@link LogRecord}.
 * The length of each {@link LogRecord} is fixed and defined by {@link #RECORD_LENGTH}.
 * This allows direct access to each {@link LogRecord} without reading the full file.
 * @author Martin Hentschel
 */
public class LogManager {
   /**
    * The only instance of this class.
    */
   private static final LogManager instance = new LogManager();
   
   /**
    * The name of the log file within a proof folder.
    */
   public static final String LOG_FILE_NAME = ".log";

   /**
    * The separator between values of a {@link LogRecord}.
    */
   private static final String CSV_SEPARATOR = ";";
   
   /**
    * The separator between different {@link LogRecord}s.
    */
   private static final String NEW_LINE = "\r\n";

   /**
    * The used charset.
    */
   private static final String CHARSET = "US-ASCII";

   /**
    * The fixed length of all saved {@link LogRecord}s.
    */
   private final int RECORD_LENGTH = toCSV(new LogRecord(LogRecordKind.BUILD, 0l, 0l, false, false, 0)).length();
   
   /**
    * Forbid instances,
    */
   private LogManager() {
   }
   
   /**
    * Saves the given {@link LogRecord} in the log file of the given {@link IProject}.
    * @param project The {@link IProject} with the log file.
    * @param record The {@link LogRecord} to save.
    * @throws CoreException Occurred Exception.
    */
   public synchronized void log(IProject project, LogRecord record) throws CoreException {
      try {
         if (project != null && record != null) {
            String content = toCSV(record);
            IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
            if (!proofFolder.exists()) {
               proofFolder.create(true, true, null);
            }
            IFile logFile = proofFolder.getFile(LOG_FILE_NAME);
            if (logFile.exists()) {
               logFile.appendContents(new ByteArrayInputStream(content.getBytes(CHARSET)), true, false, null);
            }
            else {
               logFile.create(new ByteArrayInputStream(content.getBytes()), true, null);
//               logFile.setCharset(CHARSET, null); // TODO: Setting charset requires full project access and causes trouble during build
            }
         }
      }
      catch (Exception e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * Converts the given {@link LogRecord} into a {@link String} of length {@link #RECORD_LENGTH}.
    * @param record The {@link LogRecord} to convert.
    * @return The {@link String} representing the {@link LogRecord} of length {@link #RECORD_LENGTH}.
    */
   private String toCSV(LogRecord record) {
      StringBuilder sb = new StringBuilder();
      sb.append(StringUtil.fillString(record.getKind().name(), ' ', computeMaxKindLength()));
      sb.append(CSV_SEPARATOR);
      sb.append(NumberUtil.toFullString(record.getStart()));
      sb.append(CSV_SEPARATOR);
      sb.append(NumberUtil.toFullString(record.getDuration()));
      sb.append(CSV_SEPARATOR);
      sb.append(toSingleCharacter(record.isOnlyRequiredProofs()));
      sb.append(CSV_SEPARATOR);
      sb.append(toSingleCharacter(record.isEnableThreading()));
      sb.append(CSV_SEPARATOR);
      sb.append(NumberUtil.toFullString(record.getNumberOfThreads()));
      sb.append(NEW_LINE);
      return sb.toString();
   }

   /**
    * Computes the maximal length of available {@link LogRecordKind}s.
    * @return The maximal length of {@link LogRecordKind}s.
    */
   private int computeMaxKindLength() {
      int maxLength = 0;
      for (LogRecordKind kind : LogRecordKind.values()) {
         int length = kind.name().length();
         if (length > maxLength) {
            maxLength = length;
         }
      }
      return maxLength;
   }
   
   /**
    * Counts the number of stored {@link LogRecord}s in the given {@link IProject}.
    * @param project The {@link IProject}.
    * @return The number of {@link LogRecord}s.
    * @throws IOException Occurred Exception.
    */
   public synchronized long countRecords(IProject project) throws IOException {
      IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFile logFile = proofFolder.getFile(LOG_FILE_NAME);
      if (logFile.exists()) {
         return countRecords(ResourceUtil.getLocation(logFile));
      }
      else {
         return 0;
      }
   }
   
   /**
    * Counts the number of {@link LogRecord}s in the given file.
    * @param file The {@link File} providing the {@link LogRecord}s.
    * @return The number of {@link LogRecord}s.
    * @throws IOException Occurred Exception.
    */
   public synchronized long countRecords(File file) throws IOException {
      checkFile(file);
      return file.length() / RECORD_LENGTH;
   }
   
   /**
    * Reads the {@link LogRecord} at the given index in the log file of the given {@link IProject}.
    * @param project The {@link IProject} to read from.
    * @param index The index of the {@link LogRecord} to read.
    * @return The read {@link LogRecord}.
    * @throws IOException Occurred Exception.
    */
   public synchronized LogRecord readRecord(IProject project, long index) throws IOException {
      IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
      IFile logFile = proofFolder.getFile(LOG_FILE_NAME);
      if (logFile.exists()) {
         return readRecord(ResourceUtil.getLocation(logFile), index);
      }
      else {
         return null;
      }
   }
   
   /**
    * Reads the {@link LogRecord} at the given index in the log file.
    * @param file The {@link File} to read from.
    * @param index The index of the {@link LogRecord} to read.
    * @return The read {@link LogRecord}.
    * @throws IOException Occurred Exception.
    */
   public synchronized LogRecord readRecord(File file, long index) throws IOException {
      checkFile(file);
      if (index < 0 || index > countRecords(file)) {
         throw new IOException("Invalid index '" + index + "'.");
      }
      RandomAccessFile access = new RandomAccessFile(file, "r");
      try {
         access.seek(index * RECORD_LENGTH);
         byte[] buffer = new byte[RECORD_LENGTH];
         access.read(buffer);
         return parseLogRecord(new String(buffer, CHARSET));
      }
      finally {
         access.close();
      }
   }
   
   /**
    * Converts the given {@link String} into a {@link LogRecord}.
    * @param csvRecord The {@link String} to convert.
    * @return The created {@link LogRecord}.
    * @throws IOException Occurred Exception.
    */
   private LogRecord parseLogRecord(String csvRecord) throws IOException {
      String[] values = csvRecord.split(CSV_SEPARATOR);
      return new LogRecord(LogRecordKind.valueOf(values[0].trim()), 
                           NumberUtil.parseFullLong(values[1]), 
                           NumberUtil.parseFullLong(values[2]), 
                           fromSingleCharacter(values[3]), 
                           fromSingleCharacter(values[4]), 
                           NumberUtil.parseFullInt(values[5].substring(0, values[5].length() - NEW_LINE.length())));
   }

   /**
    * Checks if the given {@link File} is a valid log file.
    * @param file The {@link File} to check.
    * @throws IOException The reason why it is not a valid log file.
    */
   public void checkFile(File file) throws IOException {
      if (file == null) {
         throw new IOException("No file defined.");
      }
      if (!file.isFile()) {
         throw new IOException("Log file does not exist.");
      }
      if (file.length() % RECORD_LENGTH != 0) {
         throw new IOException("Log file is corrupt.");
      }
   }
   
   /**
    * Converts the given boolean into a single character.
    * @param value The boolean to convert.
    * @return The single character representing the boolean value.
    */
   private char toSingleCharacter(boolean value) {
      return value ? 't' : 'f';
   }
   
   /**
    * Converts the single character into a boolean.
    * @param text The text consisting of exactly one character.
    * @return The boolean value.
    * @throws IOException Occurred Exception if not a valid text.
    */
   private boolean fromSingleCharacter(String text) throws IOException {
      if ("t".equals(text)) {
         return true;
      }
      else if ("f".equals(text)) {
         return false;
      }
      else {
         throw new IOException("Unsupported boolean \"" + text + "\".");
      }
   }

   /**
    * Checks if the given {@link IFile} is the log file ({@link #LOG_FILE_NAME}). 
    * @param file The {@link IFile} to check.
    * @return {@code true} is log file, {@code false} is something else.
    * @throws CoreException Occurred Exception.
    */
   public boolean isLogFile(IFile file) throws CoreException {
      if (file != null) {
         return LOG_FILE_NAME.equals(file.getName()) &&
                file.getParent() instanceof IFolder &&
                KeYResourcesUtil.isProofFolder((IFolder)file.getParent());
      }
      else {
         return false;
      }
   }

   /**
    * Returns the only instance of this class.
    * @return The only instance of this class.
    */
   public static LogManager getInstance() {
      return instance;
   }
}
