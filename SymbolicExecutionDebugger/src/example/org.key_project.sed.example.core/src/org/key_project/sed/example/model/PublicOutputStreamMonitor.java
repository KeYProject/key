package org.key_project.sed.example.model;

import java.io.InputStream;

import org.eclipse.debug.internal.core.OutputStreamMonitor;

/**
 * Makes the functionality of {@link OutputStreamMonitor} public available.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class PublicOutputStreamMonitor extends OutputStreamMonitor {
   /**
    * Constructor.
    * @param stream The Input stream to read from
    * @param encoding The Stream encoding or {@code null} for system default.
    */
   public PublicOutputStreamMonitor(InputStream stream, String encoding) {
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
   public void close() {
      super.close();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void kill() {
      super.kill();
   }
}
