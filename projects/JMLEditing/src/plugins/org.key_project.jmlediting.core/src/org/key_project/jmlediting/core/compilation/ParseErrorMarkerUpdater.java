package org.key_project.jmlediting.core.compilation;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.utilities.Position;
import org.key_project.util.eclipse.Logger;

public class ParseErrorMarkerUpdater {

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
            if (m.getType()
                  .equals("org.key_project.jmlediting.core.parseerror")) {

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
         final String text, final ParserException exception) {
      for (final ParserError error : exception.getAllErrors()) {
         try {
            final IMarker marker = res
                  .createMarker("org.key_project.jmlediting.core.parseerror");
            final Position pos = getPositionForOffset(text,
                  error.getErrorOffset());
            marker.setAttribute(IMarker.TEXT, error.getErrorMessage());
            marker.setAttribute(IMarker.LINE_NUMBER, pos.getLine + 1);
            marker.setAttribute(IMarker.PRIORITY, IMarker.PRIORITY_HIGH);
            marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
            marker.setAttribute(IMarker.MESSAGE, error.getErrorMessage());
            marker.setAttribute("Offset", error.getErrorOffset());

         }
         catch (final CoreException e) {
            new Logger(Activator.getDefault(), Activator.PLUGIN_ID)
                  .createErrorStatus(e);
         }

      }

   }

}
