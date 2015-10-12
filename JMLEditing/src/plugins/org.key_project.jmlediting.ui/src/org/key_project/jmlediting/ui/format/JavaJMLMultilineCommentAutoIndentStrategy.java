package org.key_project.jmlediting.ui.format;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.EditorUtility;
import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DefaultIndentLineAutoEditStrategy;
import org.eclipse.jface.text.DocumentCommand;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextUtilities;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.texteditor.ITextEditorExtension3;
import org.key_project.jmlediting.core.utilities.CommentLocator;

/**
 * The {@link JavaJMLMultilineCommentAutoIndentStrategy} format JML comments
 * correctly. It works on all comments, for all non JML comments, another given
 * {@link IAutoEditStrategy} is called.
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
public class JavaJMLMultilineCommentAutoIndentStrategy extends
DefaultIndentLineAutoEditStrategy {

   /**
    * The strategy which is wrapped and called for non JML comments.
    */
   private final IAutoEditStrategy wrappedStrategy;

   /** The partitioning that this strategy operates on. */
   private final String fPartitioning;

   /**
    * Creates a new Javadoc auto indent strategy for the given document
    * partitioning.
    *
    * @param partitioning
    *           the document partitioning
    * @param wrappedStrategy
    *           the strategy which should be called outside JML comments
    */
   public JavaJMLMultilineCommentAutoIndentStrategy(
         final IAutoEditStrategy wrappedStrategy, final String partitioning) {
      this.fPartitioning = partitioning;
      this.wrappedStrategy = wrappedStrategy;
   }

   /*
    * Unfortunately, a lot of code is copied form JavaDocAutoIndentStrategy, but
    * the code cannot be accessed. Only the inserted * are changed to @
    */

   @Override
   public void customizeDocumentCommand(final IDocument document,
         final DocumentCommand command) {
      // Detect whether JML or not
      ITypedRegion region = CommentLocator.findCommentRegion(document, command.offset);
      if (region != null && CommentLocator.isJMLComment(document.get(), region.getOffset())) {
         if (!this.isSmartMode()) {
            return;
         }

         if (command.text != null) {
            if (command.length == 0) {
               final String[] lineDelimiters = document
                     .getLegalLineDelimiters();
               final int index = TextUtilities.endsWith(lineDelimiters,
                     command.text);
               if (index > -1) {
                  // ends with line delimiter
                  if (lineDelimiters[index].equals(command.text)) {
                     // just the line delimiter
                     this.indentAfterNewLine(document, command);
                  }
                  return;
               }
            }

            if (command.text.equals("/")) { //$NON-NLS-1$
               this.indentAfterCommentEnd(document, command);
               return;
            }
         }
      }
      else {
         this.wrappedStrategy.customizeDocumentCommand(document, command);
      }
   }

   /**
    * Copies the indentation of the previous line and adds a star. If the
    * Javadoc just started on this line add standard method tags and close the
    * Javadoc.
    *
    * @param d
    *           the document to work on
    * @param c
    *           the command to deal with
    */
   private void indentAfterNewLine(final IDocument d, final DocumentCommand c) {

      final int offset = c.offset;
      if (offset == -1 || d.getLength() == 0) {
         return;
      }

      try {
         int p = 0;
         if (offset == d.getLength()) {
            p = offset - 1;
         }
         else {
            p = offset;
         }
         final IRegion line = d.getLineInformationOfOffset(p);

         final int lineOffset = line.getOffset();
         final int firstNonWS = this.findEndOfWhiteSpace(d, lineOffset, offset);
         Assert.isTrue(firstNonWS >= lineOffset,
               "indentation must not be negative"); //$NON-NLS-1$

         final StringBuffer buf = new StringBuffer(c.text);
         final IRegion prefix = this.findPrefixRange(d, line);
         final String indentation = d.get(prefix.getOffset(),
               prefix.getLength());
         final int lengthToAdd = Math.min(offset - prefix.getOffset(),
               prefix.getLength());

         buf.append(indentation.substring(0, lengthToAdd));

         if (firstNonWS < offset) {
            if (d.getChar(firstNonWS) == '/') {
               // Javadoc started on this line
               buf.append("  @ "); //$NON-NLS-1$

               if (this
                     .isPreferenceTrue(PreferenceConstants.EDITOR_CLOSE_JAVADOCS)
                     && this.isNewComment(d, offset)) {
                  c.shiftsCaret = false;
                  c.caretOffset = c.offset + buf.length();
                  final String lineDelimiter = TextUtilities
                        .getDefaultLineDelimiter(d);

                  final int eolOffset = lineOffset + line.getLength();
                  final int replacementLength = eolOffset - p;
                  final String restOfLine = d.get(p, replacementLength);
                  final String endTag = lineDelimiter + indentation + "  @*/"; //$NON-NLS-1$

                  c.length = replacementLength;
                  buf.append(restOfLine);
                  buf.append(endTag);

               }

            }
         }

         // move the caret behind the prefix, even if we do not have to insert
         // it.
         if (lengthToAdd < prefix.getLength()) {
            c.caretOffset = offset + prefix.getLength() - lengthToAdd;
         }
         c.text = buf.toString();

      }
      catch (final BadLocationException excp) {
         // stop work
      }
   }

   /**
    * Returns the value of the given boolean-typed preference.
    *
    * @param preference
    *           the preference to look up
    * @return the value of the given preference in the Java plug-in's default
    *         preference store
    */
   private boolean isPreferenceTrue(final String preference) {
      return JavaPlugin.getDefault().getPreferenceStore()
            .getBoolean(preference);
   }

   /**
    * Returns the range of the Javadoc prefix on the given line in
    * <code>document</code>. The prefix greedily matches the following regex
    * pattern: <code>\w*\*\w*</code>, that is, any number of whitespace
    * characters, followed by an asterisk ('*'), followed by any number of
    * whitespace characters.
    *
    * @param document
    *           the document to which <code>line</code> refers
    * @param line
    *           the line from which to extract the prefix range
    * @return an <code>IRegion</code> describing the range of the prefix on the
    *         given line
    * @throws BadLocationException
    *            if accessing the document fails
    */
   private IRegion findPrefixRange(final IDocument document, final IRegion line)
         throws BadLocationException {
      final int lineOffset = line.getOffset();
      final int lineEnd = lineOffset + line.getLength();
      int indentEnd = this.findEndOfWhiteSpace(document, lineOffset, lineEnd);
      if (indentEnd < lineEnd && document.getChar(indentEnd) == '@') {
         indentEnd++;
         while (indentEnd < lineEnd && document.getChar(indentEnd) == ' ') {
            indentEnd++;
         }
      }
      return new Region(lineOffset, indentEnd - lineOffset);
   }

   /**
    * Unindents a typed slash ('/') if it forms the end of a comment.
    *
    * @param d
    *           the document
    * @param c
    *           the command
    */
   private void indentAfterCommentEnd(final IDocument d, final DocumentCommand c) {
      if (c.offset < 2 || d.getLength() == 0) {
         return;
      }
      try {
         if ("* ".equals(d.get(c.offset - 2, 2))) { //$NON-NLS-1$
            // modify document command
            c.length++;
            c.offset--;
         }
      }
      catch (final BadLocationException excp) {
         // stop work
      }
   }

   /**
    * Guesses if the command operates within a newly created Javadoc comment or
    * not. If in doubt, it will assume that the Javadoc is new.
    *
    * @param document
    *           the document
    * @param commandOffset
    *           the command offset
    * @return <code>true</code> if the comment should be closed,
    *         <code>false</code> if not
    */
   private boolean isNewComment(final IDocument document,
         final int commandOffset) {

      try {
         final int lineIndex = document.getLineOfOffset(commandOffset) + 1;
         if (lineIndex >= document.getNumberOfLines()) {
            return true;
         }

         final IRegion line = document.getLineInformation(lineIndex);
         final ITypedRegion partition = TextUtilities.getPartition(document,
               this.fPartitioning, commandOffset, false);
         final int partitionEnd = partition.getOffset() + partition.getLength();
         if (line.getOffset() >= partitionEnd) {
            return false;
         }

         if (document.getLength() == partitionEnd) {
            return true; // partition goes to end of document - probably a new
            // comment
         }

         final String comment = document.get(partition.getOffset(),
               partition.getLength());
         if (comment.indexOf("/*", 2) != -1) {
            return true; // enclosed another comment -> probably a new comment
         }

         return false;

      }
      catch (final BadLocationException e) {
         return false;
      }
   }

   private boolean isSmartMode() {
      final IWorkbenchPage page = JavaPlugin.getActivePage();
      if (page != null) {
         final IEditorPart part = page.getActiveEditor();
         if (part instanceof ITextEditorExtension3) {
            final ITextEditorExtension3 extension = (ITextEditorExtension3) part;
            return extension.getInsertMode() == ITextEditorExtension3.SMART_INSERT;
         }
         else if (EditorUtility.isCompareEditorInput(part.getEditorInput())) {
            final ITextEditorExtension3 extension = (ITextEditorExtension3) part
                  .getAdapter(ITextEditorExtension3.class);
            if (extension != null) {
               return extension.getInsertMode() == ITextEditorExtension3.SMART_INSERT;
            }
         }
      }
      return false;
   }

}
