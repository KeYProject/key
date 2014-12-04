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
import org.key_project.jmlediting.ui.extension.Comment;
import org.key_project.jmlediting.ui.extension.JMLLocator;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * An {@link IJavaEditorTextHover} to support JML.
 *
 * @author Martin Hentschel
 */
public class JMLTextHover implements IJavaEditorTextHover {

   private IEditorPart editorPart;

   /**
    * {@inheritDoc}
    */
   @Override
   public String getHoverInfo(final ITextViewer textViewer, IRegion hoverRegion) {
      System.out.println("Got " + hoverRegion);
      final int offset = hoverRegion.getOffset();
      // if (hoverRegion.getLength() == 0) {
      hoverRegion = this.getHoverRegion(textViewer, hoverRegion.getOffset());
      // }
      if (hoverRegion == null) {
         return null;
      }
      System.out.println("Got " + hoverRegion);
      final IProject activeProject = WorkbenchUtil.getProject(this.editorPart);
      if (activeProject == null) {
         return null;
      }
      final IJMLParser parser = JMLPreferencesHelper
            .getProjectActiveJMLProfile(activeProject).createParser();
      try {
         final IASTNode result = parser.parse(textViewer.getDocument().get(),
               hoverRegion.getOffset() + 3, hoverRegion.getOffset()
                     + hoverRegion.getLength() - 2);
         final IASTNode selectedNode = Nodes.getDepthMostNodeWithPosition(
               offset, result);
         if (selectedNode != null && Nodes.isKeyword(selectedNode)) {
            final IKeywordNode selectedKNode = (IKeywordNode) selectedNode;
            return selectedKNode.getKeyword().getDescription();
         }
      }
      catch (final ParserException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
         return "Unable to parse JML";
      }
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IRegion getHoverRegion(final ITextViewer textViewer, final int offset) {
      final JMLLocator locator = new JMLLocator(textViewer.getDocument().get());
      final Comment jmlComment = locator.getJMLComment(offset);
      if (jmlComment != null) {
         System.out.println("Comment:" + jmlComment.getOffset() + " "
               + jmlComment.getEnd());
         return new Region(jmlComment.getOffset(), jmlComment.getEnd()
               - jmlComment.getOffset());
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
