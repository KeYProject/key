package org.key_project.jmlediting.core.marker;

import org.eclipse.core.internal.resources.Marker;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Status;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class ParseErrorMarkerUpdater {

   private static class Position {
      int line;
      int column;

      public Position(final int line, final int column) {
         super();
         this.line = line;
         this.column = column;
      }

   }

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

   public static void createErrorMarkers(final IResource res,
         final String text, final ParserException exception,
         final CommentRange surroundingComment) throws CoreException {
      try {

         // Remove all markers in this resource
         final IMarker[] problems = res.findMarkers(IMarker.PROBLEM, true, 0);

         for (final IMarker m : problems) {
            if (m.getType()
                  .equals("org.key_project.jmlediting.core.parseerror")) {
               final int markerOffset = m.getAttribute("Offset", -1);
               if (markerOffset == -1) {
                  continue;
               }
               if (surroundingComment.getBeginOffset() <= markerOffset
                     && markerOffset <= surroundingComment.getEndOffset()) {

                  m.delete();
               }
            }
         }
      }
      catch (final CoreException e) {
         // Something went wrong but should not occur
         throw new CoreException(new Status(Status.ERROR, Activator.PLUGIN_ID,
               "Failed to delete old marker", e));
      }
      // Add no markers if there is no exception
      // System.out.println("Annotation Model: " + model);
      // if (exception == null) {
      // return;
      // }
      // Create a marker for each error
      for (final ParserError error : exception.getAllErrors()) {
         try {
            final IMarker marker = res
                  .createMarker("org.key_project.jmlediting.core.parseerror");
            final Position pos = getPositionForOffset(text,
                  error.getErrorOffset());
            marker.setAttribute(Marker.TEXT, error.getErrorMessage());
            marker.setAttribute(Marker.LINE_NUMBER, pos.line + 1);
            marker.setAttribute(Marker.PRIORITY, Marker.PRIORITY_HIGH);
            marker.setAttribute(Marker.SEVERITY, Marker.SEVERITY_ERROR);
            marker.setAttribute(Marker.MESSAGE, error.getErrorMessage());
            marker.setAttribute("Offset", error.getErrorOffset());

         }
         catch (final CoreException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
         }

      }

   }

}
