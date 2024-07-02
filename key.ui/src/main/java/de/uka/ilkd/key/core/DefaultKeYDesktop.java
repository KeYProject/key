package de.uka.ilkd.key.core;

import java.awt.Desktop;
import java.awt.Desktop.Action;
import java.io.File;
import java.io.IOException;
import java.net.URI;

/**
 * The default {@link KeYDesktop} implementation delegating all requests
 * to {@link Desktop}.
 * @author Martin Hentschel
 * @see Main#getKeyDesktop()
 */
public class DefaultKeYDesktop implements KeYDesktop {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsEdit() {
      return Desktop.isDesktopSupported() && Desktop.getDesktop().isSupported(Action.EDIT);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void edit(File file) throws IOException {
      Desktop.getDesktop().edit(file);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsOpen() {
      return Desktop.isDesktopSupported() && Desktop.getDesktop().isSupported(Action.OPEN);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void open(File file) throws IOException {
      Desktop.getDesktop().open(file);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsBrowse() {
      return Desktop.isDesktopSupported() && Desktop.getDesktop().isSupported(Action.BROWSE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void browse(URI uri) throws IOException {
      Desktop.getDesktop().browse(uri);
   }
}
