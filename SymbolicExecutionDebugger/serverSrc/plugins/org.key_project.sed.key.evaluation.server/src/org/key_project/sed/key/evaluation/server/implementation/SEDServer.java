package org.key_project.sed.key.evaluation.server.implementation;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

import org.key_project.sed.key.evaluation.model.util.ServerSettings;
import org.key_project.sed.key.evaluation.server.io.FileStorage;

/**
 * The server which runs forever and listens for client connections.
 * @author Martin Hentschel
 */
public class SEDServer {
   /**
    * The program entry point.
    * @param args The start parameter.
    */
   public static void main(String[] args) {
      try {
         // Start server
         System.out.println("Forms will be stored at " + FileStorage.FORM_STORAGE_LOCATION);
         start();
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
   public static void start() throws IOException {
      ServerSocket ss = new ServerSocket(ServerSettings.PORT);
      try {
         System.out.println("Server running at port " + ss.getLocalPort() + ".");
         while (true) {
            try {
               Socket socket = ss.accept();
               new ClientThread(socket).start();
            }
            catch (Exception e) {
               e.printStackTrace();
            }
         }
      }
      finally {
         ss.close();
      }
   }
}
