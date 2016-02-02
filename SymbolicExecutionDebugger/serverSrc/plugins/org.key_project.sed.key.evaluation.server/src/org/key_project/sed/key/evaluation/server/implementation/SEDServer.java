package org.key_project.sed.key.evaluation.server.implementation;

import java.io.File;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.util.ServerPreferences;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.random.RandomCompletionManager;
import org.key_project.sed.key.evaluation.server.random.ReviewingCodeRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.report.HTMLReportEngine;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;

/**
 * The server which runs forever and listens for client connections.
 * @author Martin Hentschel
 */
public class SEDServer {
   /**
    * The start argument of {@link #main(String[])} to create a report
    * for all available {@link AbstractEvaluation}s instead of starting the server.
    */
   public static final String REPORT_START_ARGUMENT = "-reports";
   
   /**
    * The storage location to use.
    */
   private final File storageLocation;
   
   /**
    * The port to open.
    */
   private final int port;
   
   /**
    * The currently used server socket.
    */
   private ServerSocket serverSocket;

   /**
    * Constructor.
    * @param storageLocation The storage location to use.
    * @param port The port to open.
    */
   public SEDServer(File storageLocation, int port) {
      // Store instance variables
      this.storageLocation = storageLocation;
      this.port = port;
      // Index random completions
      System.out.println("Indexing random proof attempts completion.");
      RandomCompletionManager.registerRandomCompletion(UnderstandingProofAttemptsEvaluation.RANDOM_COMPUTER_NAME,
                                                       new UnderstandingProofAttemptsRandomFormOrderComputer(storageLocation));
      RandomCompletionManager.registerRandomCompletion(ReviewingCodeEvaluation.RANDOM_COMPUTER_NAME,
                                                       new ReviewingCodeRandomFormOrderComputer(storageLocation));
      // Print information about storage location
      System.out.println("Forms will be stored at " + storageLocation);
   }

   /**
    * The program entry point.
    * @param args The start parameter.
    */
   public static void main(String[] args) {
      try {
         if (ArrayUtil.contains(args, REPORT_START_ARGUMENT)) {
            createReports();
         }
         else {
            SEDServer server = new SEDServer(FileStorage.FORM_STORAGE_LOCATION, ServerPreferences.getPort());
            server.start();
         }
      }
      catch (Exception e) {
         e.printStackTrace();
      }
   }
   
   /**
    * Creates HTML reports for all available {@link AbstractEvaluation}s.
    * @throws Exception Occurred Exception.
    */
   public static void createReports() throws Exception {
      System.out.println("Creating reports...");
      for (AbstractEvaluation evaluation: AbstractEvaluation.getEvaluations()) {
         File target = new File(FileStorage.FORM_STORAGE_LOCATION, IOUtil.validateOSIndependentFileName(evaluation.getName()) + ".html");
         HTMLReportEngine engine = new HTMLReportEngine(FileStorage.FORM_STORAGE_LOCATION);
         if (engine.saveReport(evaluation, target)) {
            System.out.println("Report created: " + target.getAbsolutePath());
         }
      }
   }

   /**
    * Starts listening for client requests.
    * This method only terminates if the {@link ServerSocket} can't be opened.
    * @throws IOException Occurred Exception.
    */
   public void start() throws IOException {
      if (!isRunning()) {
         // Open socket
         serverSocket = new ServerSocket(port);
         try {
            System.out.println("Server running at port " + serverSocket.getLocalPort() + ".");
            while (isRunning()) {
               try {
                  Socket socket = serverSocket.accept();
                  new ClientThread(storageLocation, socket).start();
               }
               catch (Exception e) {
                  if (isRunning()) {
                     e.printStackTrace();
                  }
               }
            }
         }
         finally {
            if (serverSocket != null) {
               serverSocket.close();
            }
         }
      }
   }
   
   /**
    * Checks if the server is currently open.
    * @return {@code true} running, {@code false} stopped.
    */
   public boolean isRunning() {
      return serverSocket != null && serverSocket.isBound() && !serverSocket.isClosed();
   }

   /**
    * Stops the currently running server.
    */
   public void stop() {
      try {
         if (isRunning()) {
            serverSocket.close();
            serverSocket = null;
         }
      }
      catch (IOException e) {
         e.printStackTrace();
      }
   }
}
