package org.key_project.sed.key.evaluation.io;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.Socket;

import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.util.ServerPreferences;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.ObjectUtil;

public class SendThread extends Thread {
   private final String message;
   
   private final String host;
   
   private final int port;
   
   private final boolean parseAnser;
   
   private String answer;
   
   private EvaluationInput answerInput;
   
   private Exception exception;
   
   private Socket socket;
   
   private ObjectOutputStream out;
   
   private ObjectInputStream in;
   
   private long time;
   
   public SendThread(String message) {
      this(message, ServerPreferences.getHost(), ServerPreferences.getPort());
   }

   public SendThread(String message, String host, int port) {
      this(message, host, port, true);
   }

   public SendThread(String message, String host, int port, boolean parseAnser) {
      this.message = message;
      this.host = host;
      this.port = port;
      this.parseAnser = parseAnser;
   }

   @Override
   public void run() {
      long start = System.currentTimeMillis();
      try {
         socket = new Socket(host, port);
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
            if (parseAnser) {
               answerInput = EvaluationInputReader.parse(answer);
            }
         }
         catch (ClassNotFoundException e) {
            throw new IOException("Can't handle answer.", e);
         }
         finally {
            closeConnection();
         }
      }
      catch (Exception e) {
         exception = e;
      }
      finally {
         time = System.currentTimeMillis() - start;
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

   public Exception getException() {
      return exception;
   }

   public long getTime() {
      return time;
   }

   /**
    * Pings the specified server.
    * @param host The host.
    * @param port The port.
    * @return The elapsed time.
    * @throws Exception Occurred Exception.
    */
   public static long ping(String host, int port) throws Exception {
      SendThread thread = new SendThread("Ping", host, port, false);
      thread.run();
      if (thread.getException() != null) {
         throw thread.getException();
      }
      return thread.getTime();
   }

   /**
    * Updates the page order on the target {@link EvaluationInput} with the values from the source {@link EvaluationInput}.
    * @param target The target {@link EvaluationInput} to modify.
    * @param source The source {@link EvaluationInput} to read from.
    */
   public static void updatePageOrder(EvaluationInput target, EvaluationInput source) {
      for (AbstractFormInput<?> answerFormInput : source.getFormInputs()) {
         if (answerFormInput instanceof RandomFormInput) {
            RandomFormInput randomAnswer = (RandomFormInput) answerFormInput;
            if (!CollectionUtil.isEmpty(randomAnswer.getPageOrder())) {
               RandomFormInput form = (RandomFormInput) target.getFormInput(randomAnswer.getForm());
               form.setPageOrder(randomAnswer.getPageOrder());
               for (AbstractPageInput<?> pageInput : form.getPageInputs()) {
                  Tool tool = randomAnswer.getTool(randomAnswer.getPageInput(pageInput.getPage()));
                  form.setTool(pageInput, tool);
               }
            }
         }
      }
   }

   /**
    * Copies the UUID from the source {@link EvaluationInput} to the target {@link EvaluationInput}.
    * @param target The target {@link EvaluationInput} to modify.
    * @param source The source {@link EvaluationInput} to read from.
    * @throws InvocationTargetException Occurred Exception.
    */
   public static void updateUUID(EvaluationInput target, EvaluationInput source) throws InvocationTargetException {
      if (target.getUUID() == null) {
         target.setUUID(source.getUUID());
      }
      else {
         if (!target.getUUID().equals(source.getUUID())) {
            throw new InvocationTargetException(null, "Received answer does not fit with current evaluation results.");
         }
      }
   }
}
