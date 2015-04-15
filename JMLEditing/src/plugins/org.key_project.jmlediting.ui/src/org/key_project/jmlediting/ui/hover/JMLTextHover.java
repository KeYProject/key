package org.key_project.jmlediting.ui.hover;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.ui.text.java.hover.IJavaEditorTextHover;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.ui.IEditorPart;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * An {@link IJavaEditorTextHover} to support JML. Currently it shows
 * description hovers for keywords.
 *
 * @author Martin Hentschel, Moritz Lichter
 */
public class JMLTextHover implements IJavaEditorTextHover {

   private IEditorPart editorPart;

   /**
    * {@inheritDoc}
    */
   @Override
   public String getHoverInfo(final ITextViewer textViewer,
         final IRegion hoverRegion) {
      if (!JMLPreferencesHelper.isAnyProfileAvailable()) {
         return null;
      }
      // Calculate the hover region, we want to use
      final int cursorPosition = hoverRegion.getOffset();
      // That is the complete JML Comment
      final CommentRange comment = this.getJMLComment(textViewer,
            cursorPosition);
      if (comment == null) {
         // No JML comment, du not provide a hover
         return null;
      }

      // Parse the comment according to the gi
      final IProject activeProject = WorkbenchUtil.getProject(this.editorPart);
      if (activeProject == null) {
         return null;
      }
      final IJMLParser parser = JMLPreferencesHelper
            .getProjectActiveJMLProfile(activeProject).createParser();
      IASTNode result;
      try {
         // Parse the text
         // End index of comment is inclusive, but input end for parser
         // exclusive
         result = parser.parse(textViewer.getDocument().get(), comment);

      }
      catch (final ParserException e) {
         result = e.getErrorNode();
         if (result == null) {
            return "Unable to parse JML";
         }
      }
      final IASTNode selectedNode = Nodes.getDepthMostNodeWithPosition(
            cursorPosition, result);
      if (selectedNode != null && Nodes.isKeyword(selectedNode)) {
         final IKeywordNode selectedKNode = (IKeywordNode) selectedNode;
         return selectedKNode.getKeyword().getDescription();
      }
      return null;
   }

   private CommentRange getJMLComment(final ITextViewer textViewer,
         final int offset) {
      final CommentLocator locator = new CommentLocator(textViewer
            .getDocument().get());
      final CommentRange jmlComment = locator.getJMLComment(offset);
      return jmlComment;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IRegion getHoverRegion(final ITextViewer textViewer, final int offset) {
      final CommentRange jmlComment = this.getJMLComment(textViewer, offset);
      if (jmlComment != null) {
         return new Region(jmlComment.getContentBeginOffset(),
               jmlComment.getContentLength());
      }
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setEditor(final IEditorPart editor) {
      this.editorPart = editor;
   }
}
