package org.key_project.sed.example.model;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.eclipse.debug.core.model.IStreamMonitor;
import org.eclipse.debug.core.model.IStreamsProxy;
import org.eclipse.debug.core.model.IStreamsProxy2;

/**
 * An {@link IStreamsProxy} for arbitrary streams.
 * @author Martin Hentschel
 */
public class CustomStreamsProxy implements IStreamsProxy, IStreamsProxy2 {
   /**
    * The encoding used by default.
    */
   public static final String DEFAULT_ENCODING = "UTF-8";
   
   /**
    * The used {@link IStreamMonitor} for the error stream.
    */
   private final PublicOutputStreamMonitor errorStreamMonitor;

   /**
    * The used {@link IStreamMonitor} for the output stream.
    */
   private final PublicOutputStreamMonitor outputStreamMonitor;

   /**
    * The used {@link IStreamMonitor} for the input stream.
    */
   private final PublicInputStreamMonitor inputStreamMonitor;

   /**
    * Constructor.
    * @param out The {@link InputStream} from which the output should be read.
    * @param errOut The {@link InputStream} from which the error output should be read.
    * @param in The {@link OutputStream} to write input to.
    */
   public CustomStreamsProxy(InputStream out, InputStream errOut, OutputStream in) {
      if (errOut != null) {
         errorStreamMonitor = new PublicOutputStreamMonitor(errOut, DEFAULT_ENCODING);
         errorStreamMonitor.startMonitoring();
      }
      else {
         errorStreamMonitor = null;
      }
      if (out != null) {
         outputStreamMonitor = new PublicOutputStreamMonitor(out, DEFAULT_ENCODING);
         outputStreamMonitor.startMonitoring();
      }
      else {
         outputStreamMonitor = null;
      }
      if (in != null) {
         inputStreamMonitor = new PublicInputStreamMonitor(in, DEFAULT_ENCODING);
         inputStreamMonitor.startMonitoring();
      }
      else {
         inputStreamMonitor = null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IStreamMonitor getErrorStreamMonitor() {
      return errorStreamMonitor;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IStreamMonitor getOutputStreamMonitor() {
      return outputStreamMonitor;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void write(String input) throws IOException {
      if (inputStreamMonitor != null) {
         inputStreamMonitor.write(input);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void closeInputStream() throws IOException {
      if (inputStreamMonitor != null) {
         inputStreamMonitor.closeInputStream();
      }
   }
   
   /**
    * Closes all monitors.
    */
   public void close() {
      if (errorStreamMonitor != null) {
         errorStreamMonitor.close();
      }
      if (outputStreamMonitor != null) {
         outputStreamMonitor.close();
      }
      if (inputStreamMonitor != null) {
         inputStreamMonitor.close();
      }
   }
   
   /**
    * Kills all monitors.
    */
   public void kill() {
      if (errorStreamMonitor != null) {
         errorStreamMonitor.kill();
      }
      if (outputStreamMonitor != null) {
         outputStreamMonitor.kill();
      }
      if (inputStreamMonitor != null) {
         inputStreamMonitor.close();
      }
   }
}