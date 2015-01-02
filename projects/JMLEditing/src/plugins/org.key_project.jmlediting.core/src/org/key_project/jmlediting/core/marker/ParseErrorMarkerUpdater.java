package org.key_project.jmlediting.core.marker;

import org.eclipse.core.internal.resources.Marker;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;

public class ParseErrorMarkerUpdater {

   public static void createErrorMarkers(final IResource res,
         final IDocument doc, final ParserException exception) {
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
         // something went wrong
      }
      // Add no markers if there is no exception
      if (exception == null) {
         return;
      }
      // Create a marker for each error
      for (final ParserError error : exception.getAllErrors()) {
         try {
            final IMarker marker = res
                  .createMarker("org.key_project.jmlediting.core.parseerror");
            marker.setAttribute(Marker.TEXT, error.getErrorMessage());
            marker.setAttribute(Marker.LINE_NUMBER,
                  doc.getLineOfOffset(error.getErrorOffset()) + 1);
            marker.setAttribute(Marker.PRIORITY, Marker.PRIORITY_HIGH);
            marker.setAttribute(Marker.SEVERITY, Marker.SEVERITY_ERROR);
            marker.setAttribute(Marker.MESSAGE, error.getErrorMessage());
         }
         catch (final CoreException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
         }
         catch (final BadLocationException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
         }

      }

   }

}
