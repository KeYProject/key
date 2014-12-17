package org.key_project.jmlediting.ui.highlighting;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.presentation.IPresentationDamager;
import org.eclipse.jface.text.presentation.IPresentationRepairer;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * A Modified DefaultDamagerRepairer as it is used by the
 * JavaSourceViewerConiguration. It adapts the results of the original functions
 * to allow Comment Highlighting for JML and Keyword Highlighting for JML
 *
 * @author David Giessing
 */
public class JMLPresentationDamagerRepairer implements IPresentationDamager,
IPresentationRepairer {

   /**
    * The original instance of DefaultDamagerRepairer currently in use for
    * JavaComments.
    */
   private final DefaultDamagerRepairer wrappedInstance;

   /**
    * The document that the DamagerRepairer is used on.
    */
   private IDocument doc;

   /**
    * The EditorPart, where this object is used for.
    */
   private final IEditorPart editorPart;

   /**
    * Constructor for JML PresentationDamagerRepairer that stores the
    * wrappedInstance.
    *
    * @param wrappedInstance
    *           the
    * @param part
    *           the {@link IEditorPart} this object is used for
    */
   public JMLPresentationDamagerRepairer(
         final DefaultDamagerRepairer wrappedInstance, final IEditorPart part) {
      super();
      this.wrappedInstance = wrappedInstance;
      this.editorPart = part;
   }

   /**
    * {@inheritDoc} Creates the default presentation if the damage is not in a
    * JML section if the damage is in a JML content Section the Presentation is
    * displayed in the Global JML Color, which is defined in the Global Property
    * page. If there are project specific settings, the color in the projects
    * ColorPage is used.
    */
   @Override
   public void createPresentation(final TextPresentation presentation,
         final ITypedRegion damage) {
      boolean jml = false;
      final RGB jmlColor = JMLUiPreferencesHelper.getWorkspaceJMLColor();
      final CommentLocator locator = new CommentLocator(this.doc.get());
      jml = locator.isInJMLcomment(damage.getOffset());
      final TextAttribute ta;
      if (jml) {
         ta = new TextAttribute(new Color(Display.getDefault(), jmlColor.red,
               jmlColor.green, jmlColor.blue));
         this.addRange(presentation, damage.getOffset(), damage.getLength(), ta);
      }
      else {
         // Normal Java Comment
         this.wrappedInstance.createPresentation(presentation, damage);
      }
   }

   @Override
   public void setDocument(final IDocument document) {
      this.doc = document;
      this.wrappedInstance.setDocument(document);
   }

   /**
    * {@inheritDoc}
    *
    * @return the original DamageRegion when the DamageOffset is not done in the
    *         First Line of a Comment. If the Damage Offset is in the first Line
    *         of a Comment the whole Comment has to be redisplayed which results
    *         in an extension of the Damage Region to the whole CommentRange
    */
   @Override
   public IRegion getDamageRegion(final ITypedRegion partition,
         final DocumentEvent event, final boolean documentPartitioningChanged) {
      final IRegion damage = this.wrappedInstance.getDamageRegion(partition,
            event, documentPartitioningChanged);
      final CommentLocator locator = new CommentLocator(this.doc.get());
      final CommentRange surroundingComment = locator.getCommentOfOffset(event
            .getOffset()); // the Comment surrounding the Offset, null if there
      // is no Comment surrounding the offset
      if (surroundingComment == null) {
         return damage;
      }
      else {
         return new Region(surroundingComment.getBeginOffset(),
               surroundingComment.getEndOffset()
                     - surroundingComment.getBeginOffset() + 1);
      }
   }

   /**
    * Copied from {@link DefaultDamagerRepairer}.
    *
    * Adds style information to the given text presentation. In case of a JML
    * Comment it provides Syntax Highlighting for JML Keywords. If the parser
    * can not find a valid Keyword, the normal Highlighting is used.
    *
    * @param presentation
    *           the text presentation to be extended
    * @param offset
    *           the offset of the range to be styled
    * @param length
    *           the length of the range to be styled
    * @param attr
    *           the attribute describing the style of the range to be styled
    * @throws BadLocationException
    */

   protected void addRange(final TextPresentation presentation,
         final int offset, final int length, final TextAttribute attr) {
      if (attr != null) {
         final int style = attr.getStyle();
         final int fontStyle = style & (SWT.ITALIC | SWT.BOLD | SWT.NORMAL);
         final StyleRange styleRange = new StyleRange(offset, length,
               attr.getForeground(), attr.getBackground(), fontStyle);
         styleRange.strikeout = (style & TextAttribute.STRIKETHROUGH) != 0;
         styleRange.underline = (style & TextAttribute.UNDERLINE) != 0;
         styleRange.font = attr.getFont();
         presentation.addStyleRange(styleRange);
         if (JMLPreferencesHelper.isAnyProfileAvailable()) {
            // From here it is all about Highlighting for JML Keywords
            final CommentLocator locator = new CommentLocator(this.doc.get());
            final CommentRange surroundingComment = locator
                  .getJMLComment(offset);
            // Only provide advanced SyntaxHighlighting for JML Comments
            if (locator.isInJMLcomment(offset)) {
               final IJMLProfile activeProfile = JMLPreferencesHelper
                     .getProjectActiveJMLProfile(WorkbenchUtil
                           .getProject(this.editorPart));
               final IJMLParser parser = activeProfile.createParser();
               try {
                  final IASTNode parseResult = parser.parse(this.doc.get(),
                        surroundingComment.getContentBeginOffset(),
                        surroundingComment.getContentEndOffset() + 1);
                  final List<IKeywordNode> allKeywords = Nodes
                        .getAllKeywords(parseResult);
                  int lastEnd = offset;
                  final List<StyleRange> styles = new ArrayList<StyleRange>();
                  for (final IKeywordNode kNode : allKeywords) {
                     final int keywordStartOffset = kNode.getStartOffset();
                     final int keywordEndOffset = kNode.getEndOffset();
                     // Style between last and current Keyword (or from comment
                     // begin until the start of first Keyword)
                     styles.add(new StyleRange(lastEnd, keywordStartOffset
                           - lastEnd, styleRange.foreground,
                           styleRange.background, attr.getStyle()));
                     // Style for the Keyword
                     styles.add(new StyleRange(keywordStartOffset,
                           keywordEndOffset - keywordStartOffset + 1,
                           styleRange.foreground, styleRange.background,
                           SWT.BOLD));
                     lastEnd = keywordEndOffset + 1;
                  }
                  // Adding Style after last Keyword
                  styles.add(new StyleRange(lastEnd, surroundingComment
                        .getEndOffset() - lastEnd + 1, styleRange.foreground,
                        styleRange.background, attr.getStyle()));
                  // Transfer to Array for use in MergeStyle
                  final StyleRange[] highlightedRanges = new StyleRange[styles
                        .size()];
                  for (int i = 0; i < styles.size(); i++) {
                     highlightedRanges[i] = styles.get(i);
                  }
                  presentation.mergeStyleRanges(highlightedRanges);
               }
               catch (final ParserException e) {
                  // Invalid JML Code, no advanced SyntaxColoring possible
                  // System.out.println(e.getMessage());
               }
            }
         }
      }
   }
}
