package org.key_project.sed.key.evaluation.server.implementation;

import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.Socket;
import java.util.List;

import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.random.IRandomFormOrderComputer;
import org.key_project.sed.key.evaluation.server.io.FileStorage;
import org.key_project.util.java.ObjectUtil;

/**
 * A {@link ClientThread} answers a client request.
 * @author Martin Hentschel
 */
public class ClientThread extends Thread {
   /**
    * The {@link Socket} to use.
    */
   private final Socket socket;

   /**
    * Constructor.
    * @param socket The {@link Socket} to use.
    */
   public ClientThread(Socket socket) {
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
            IRandomFormOrderComputer computer = formInput.getForm().getRandomOrderComputer();
            List<RandomFormInput> updatedOrders = computer != null ? 
                                                  computer.updateRandomOrder(evaluationInput, formInput) : 
                                                  null;
            // Store evaluation
            FileStorage.store(formInput, updatedOrders);
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
