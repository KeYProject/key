package org.key_project.jmlediting.core.compilation;

import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.utilities.Position;
import org.key_project.util.eclipse.Logger;

public class ValidationErrorMarkerUpdater {

   private static Position getPositionForOffset(final String text,
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

   public static void removeErrorMarkers(final IResource res) {
      try {

         // Remove all markers in this resource
         final IMarker[] problems = res.findMarkers(IMarker.PROBLEM, true, 0);

         for (final IMarker m : problems) {
            if (m.getType().equals(
                  "org.key_project.jmlediting.core.validationerror")) {

               m.delete();
            }
         }
      }
      catch (final CoreException e) {
         new Logger(Activator.getDefault(), Activator.PLUGIN_ID)
         .createErrorStatus(e);
      }
   }

   public static void createErrorMarkers(final IResource res,
         final String text, final List<JMLValidationError> errors) {
      for (final JMLValidationError error : errors) {
         try {
            final IMarker marker = res.createMarker(error.getErrorType());
            final Position pos = getPositionForOffset(text, error
                  .getInvalidSpec().getStartOffset());
            marker.setAttribute(IMarker.TEXT, error.getErrorMessage());
            marker.setAttribute(IMarker.LINE_NUMBER, pos.getLine() + 1);
            marker.setAttribute(IMarker.PRIORITY, IMarker.PRIORITY_HIGH);
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
            marker.setAttribute(IMarker.MESSAGE, error.getErrorMessage());
            marker.setAttribute("Offset", error.getInvalidSpec().getEndOffset());

         }
         catch (final CoreException e) {
            new Logger(Activator.getDefault(), Activator.PLUGIN_ID)
            .createErrorStatus(e);
         }

      }

   }
}
