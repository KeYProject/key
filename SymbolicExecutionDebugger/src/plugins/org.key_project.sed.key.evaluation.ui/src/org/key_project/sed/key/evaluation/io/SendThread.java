package org.key_project.sed.key.evaluation.io;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.Socket;

import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.util.ServerSettings;
import org.key_project.util.java.ObjectUtil;

public class SendThread extends Thread {
   private final String message;
   
   private String answer;
   
   private EvaluationInput answerInput;
   
   private Throwable exception;
   
   private Socket socket;
   
   private ObjectOutputStream out;
   
   private ObjectInputStream in;
   
   public SendThread(String message) {
      this.message = message;
   }

   @Override
   public void run() {
      try {
         socket = new Socket(ServerSettings.HOST, ServerSettings.PORT);
         out = null;
         in = null;
         try {
            // Open streams
            out = new ObjectOutputStream(socket.getOutputStream());
            in = new ObjectInputStream(socket.getInputStream());
            // Write message
            out.writeObject(message);
            // Read answer
            answer = ObjectUtil.toString(in.readObject());
            // Parse answer
            answerInput = EvaluationInputReader.parse(answer);
         }
         catch (ClassNotFoundException e) {
            throw new IOException("Can't handle answer.", e);
         }
         finally {
            closeConnection();
         }
      }
      catch (Throwable t) {
         exception = t;
      }
   }
   
   @SuppressWarnings("deprecation")
   public void cancel() {
      try {
         stop();
         closeConnection();
      }
      catch (Exception e) {
         // Nothing to do
      }
   }
   
   protected void closeConnection() throws IOException {
      if (out != null) {
         out.close();
      }
      if (in != null) {
         in.close();
      }
      if (socket != null) {
         socket.close();
      }
   }

   public String getAnswer() {
      return answer;
   }

   public EvaluationInput getAnswerInput() {
      return answerInput;
   }

   public Throwable getException() {
      return exception;
   }
}
