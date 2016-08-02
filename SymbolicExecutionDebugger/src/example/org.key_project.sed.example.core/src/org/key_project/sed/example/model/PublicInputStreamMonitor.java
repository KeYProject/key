package org.key_project.sed.example.model;

import java.io.IOException;
import java.io.OutputStream;

import org.eclipse.debug.internal.core.InputStreamMonitor;

/**
 * Makes the functionality of {@link InputStreamMonitor} public available.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class PublicInputStreamMonitor extends InputStreamMonitor {
   /**
    * Constructor.
    * @param stream
    */
   public PublicInputStreamMonitor(OutputStream stream) {
      super(stream);
   }

   /**
    * Constructor.
    * @param stream The output stream.
    * @param encoding The stream encoding or {@code null} for system default.
    */
   public PublicInputStreamMonitor(OutputStream stream, String encoding) {
      super(stream, encoding);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void startMonitoring() {
      super.startMonitoring();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void write(String text) {
      super.write(text);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void close() {
      super.close();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void closeInputStream() throws IOException {
      super.closeInputStream();
   }
}
