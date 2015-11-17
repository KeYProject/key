package org.key_project.sed.key.evaluation.server.implementation;

import java.io.File;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.Socket;
import java.util.List;

import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.sed.key.evaluation.server.random.IRandomCompletion;
import org.key_project.sed.key.evaluation.server.random.RandomCompletionManager;
import org.key_project.util.java.ObjectUtil;

/**
 * A {@link ClientThread} answers a client request.
 * @author Martin Hentschel
 */
public class ClientThread extends Thread {
   /**
    * The storage location.
    */
   private final File storageLocation;
   
   /**
    * The {@link Socket} to use.
    */
   private final Socket socket;

   /**
    * Constructor.
    * @param storageLocation The storage location.
    * @param socket The {@link Socket} to use.
    */
   public ClientThread(File storageLocation, Socket socket) {
      this.storageLocation = storageLocation;
      this.socket = socket;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void run() {
      ObjectInputStream in = null;
      ObjectOutputStream out = null;
      try {
         // Open streams
         in = new ObjectInputStream(socket.getInputStream());
         out = new ObjectOutputStream(socket.getOutputStream());
         // Read message
         String message = ObjectUtil.toString(in.readObject());
         // Work with message
         try {
            EvaluationInput evaluationInput = EvaluationInputReader.parse(message);
            AbstractFormInput<?> formInput = evaluationInput.getCurrentFormInput();
            // Compute random orders
            String randomOrderComputer = formInput.getForm().getRandomOrderComputerName();
            IRandomCompletion computer = RandomCompletionManager.createRandomCompletion(randomOrderComputer);
            List<RandomFormInput> updatedOrders = computer != null ? 
                                                  computer.computeRandomValues(evaluationInput, formInput) : 
                                                  null;
            // Store evaluation
            FileStorage.store(storageLocation, formInput, updatedOrders);
            // Send answer
            out.writeObject(EvaluationInputWriter.toRandomOrderXML(evaluationInput, updatedOrders));
         }
         catch (Exception e) {
            // Send answer
            out.writeObject("Unknown request: " + e.getMessage());
         }
      }
      catch (Exception e) {
         e.printStackTrace();
      }
      finally {
         try {
            if (in != null) {
               in.close();
            }
            if (out != null) {
               out.close();
            }
            socket.close();
         }
         catch (Exception e) {
            e.printStackTrace();
         }
      }
   }
}
