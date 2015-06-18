package org.key_project.sed.key.evaluation.server.implementation;

import java.io.File;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.util.ServerSettings;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.random.RandomCompletionManager;
import org.key_project.sed.key.evaluation.server.random.UnderstandingProofAttemptsRandomFormOrderComputer;

/**
 * The server which runs forever and listens for client connections.
 * @author Martin Hentschel
 */
public class SEDServer {
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
      UnderstandingProofAttemptsRandomFormOrderComputer computer = new UnderstandingProofAttemptsRandomFormOrderComputer(storageLocation);
      RandomCompletionManager.registerRandomCompletion(UnderstandingProofAttemptsEvaluation.RANDOM_COMPUTER_NAME, computer);
      // Print information about storage location
      System.out.println("Forms will be stored at " + storageLocation);
   }

   /**
    * The program entry point.
    * @param args The start parameter.
    */
   public static void main(String[] args) {
      try {
         SEDServer server = new SEDServer(FileStorage.FORM_STORAGE_LOCATION, ServerSettings.PORT);
         server.start();
      }
      catch (Exception e) {
         e.printStackTrace();
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
