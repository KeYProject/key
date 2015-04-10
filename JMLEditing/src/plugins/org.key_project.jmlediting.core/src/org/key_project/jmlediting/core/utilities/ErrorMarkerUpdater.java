package org.key_project.jmlediting.core.utilities;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

/**
 * Class responsible for updating the ErrorMarkers in a Resource.
 *
 * @author David Giessing
 *
 */
public class ErrorMarkerUpdater {

   /**
    * Converts an offset into a Position.
    *
    * @param text
    *           the text to operate on
    * @param offset
    *           the offset to convert
    * @return the Position of the offset or null if offset is not inside the
    *         texts range
    */
   protected static Position getPositionForOffset(final String text,
         final int offset) {
      final char[] textc = text.toCharArray();
      int line = 0;
      int column = 0;
      for (int position = 0; position < textc.length; position++) {
         final char c = textc[position];
         if (c == '\r') {
            if (position + 1 < textc.length && textc[position + 1] == '\n') {
               line++;
               position++;
               column = 0;
            }
         }
         else if (c == '\n') {
            line++;
            column = 0;
         }
         else {
            column++;
         }
         if (position >= offset) {
            return new Position(line, column);
         }
      }
      return null;
   }

   /**
    * Removes all JML ErrorMarkers from res.
    *
    * @param res
    *           the Resource
    */
   public static void removeErrorMarkers(final IResource res) {
      for (final ErrorTypes e : ErrorTypes.values()) {
         try {

            // Remove all markers in this resource
            final IMarker[] problems = res
                  .findMarkers(IMarker.PROBLEM, true, 0);

            for (final IMarker m : problems) {
               if (m.getType().equals(e.getId())) {
                  m.delete();
               }
            }
         }
         catch (final CoreException exception) {
            LogUtil.getLogger().createErrorStatus(exception);
         }
      }
   }

   /**
    * Creates the Errormarkers for errors on the Resource res.
    * 
    * @param errors
    *           the errors to be displayed
    * @param res
    *           the Resource to operate on
    * @param text
    *           the source of the Resource
    */
   public static void createErrorMarker(final List<JMLError> errors,
         final IFile res, final String text) {
      for (final JMLError e : errors) {
         try {
            final IMarker marker = res.createMarker(e.getErrorType().getId());
            final Position pos = ErrorMarkerUpdater.getPositionForOffset(text,
                  e.getOffset());
            marker.setAttribute(IMarker.TEXT, e.getErrorMessage());
            marker.setAttribute(IMarker.LINE_NUMBER, pos.getLine() + 1);
            marker.setAttribute(IMarker.PRIORITY, IMarker.PRIORITY_HIGH);
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
            marker.setAttribute(IMarker.MESSAGE, e.getErrorMessage());
            marker.setAttribute("Offset", e.getOffset());

         }
         catch (final CoreException exception) {
            LogUtil.getLogger().createErrorStatus(exception);
         }
      }
   }
}
