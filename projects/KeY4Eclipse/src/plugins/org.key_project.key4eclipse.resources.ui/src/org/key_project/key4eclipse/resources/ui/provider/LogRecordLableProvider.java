package org.key_project.key4eclipse.resources.ui.provider;

import java.text.SimpleDateFormat;
import java.util.Date;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.key4eclipse.resources.log.LogRecord;

/**
 * An {@link ITableLabelProvider} to show {@link LogRecord}s.
 * @author Martin Hentschel
 */
public class LogRecordLableProvider extends LabelProvider implements ITableLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object element, int columnIndex) {
      if (element instanceof LogRecord) {
         switch (columnIndex) {
            case 0 : return ((LogRecord) element).getKind().name();
            case 1 : return toDate(((LogRecord) element).getStart());
            case 2 : return toDuration(((LogRecord) element).getDuration());
            case 3 : return Boolean.toString(((LogRecord) element).isOnlyRequiredProofs());
            case 4 : return Boolean.toString(((LogRecord) element).isEnableThreading());
            case 5 : return Integer.toString(((LogRecord) element).getNumberOfThreads());
            default : return null;
         }
      }
      else if (element instanceof Throwable) {
         if (columnIndex == 0) {
            return ((Throwable) element).getMessage();
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Converts the given duration into seconds.
    * @param duration The duration to convert.
    * @return The duration in seconds.
    */
   protected String toDuration(long duration) {
      long seconds = duration / 1000;
      return seconds + " s";
   }

   /**
    * Converts the given timestamp into a human readable date.
    * @param timestamp The timestamp.
    * @return The human readable date.
    */
   protected String toDate(long timestamp) {
      Date date = new Date(timestamp);
      return SimpleDateFormat.getInstance().format(date);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getColumnImage(Object element, int columnIndex) {
      return null;
   }
}
