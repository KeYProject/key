package org.key_project.ui.util;

import java.awt.Desktop;
import java.io.File;
import java.io.IOException;
import java.net.URI;

import org.eclipse.swt.program.Program;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.core.KeYDesktop;

/**
 * Implementation of {@link KeYDesktop} which avoids {@link Desktop} functionality
 * which is sometimes buggy under Linux by using SWT functionality instead.
 * @author Martin Hentschel
 */
public class EclipseKeYDesktop implements KeYDesktop {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsEdit() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void edit(File file) throws IOException {
      open(file);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsOpen() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void open(final File file) throws IOException {
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            try {
               Program.launch(file.getAbsolutePath());
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);
               LogUtil.getLogger().openErrorDialog(null, e);
            }
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsBrowse() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void browse(final URI uri) throws IOException {
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            try {
               Program.launch(uri.toString());
//               WebBrowserEditor.open(new WebBrowserEditorInput(uri.toURL()));
            }
            catch (Exception e) {
               LogUtil.getLogger().logError(e);
               LogUtil.getLogger().openErrorDialog(null, e);
            }
         }
      });
   }
}
