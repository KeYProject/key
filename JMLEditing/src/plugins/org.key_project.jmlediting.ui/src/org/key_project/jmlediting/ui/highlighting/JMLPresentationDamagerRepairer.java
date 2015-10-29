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
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;
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
      final RGB jmlColor = JMLUiPreferencesHelper
            .getWorkspaceJMLColor(ColorProperty.COMMENT);
      final CommentRange surroundingComment = CommentLocator.getJMLComment(doc.get(), damage);
      final TextAttribute ta;
      if (surroundingComment != null) {
         // JML Comment
         ta = new TextAttribute(new Color(Display.getCurrent(), jmlColor));
         this.modifyPresentationForJMLComment(presentation, ta,
               surroundingComment);
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
      final CommentRange surroundingComment = CommentLocator.getComment(doc.get(), partition);
      // is no Comment surrounding the offset
      if (surroundingComment == null) {
         return damage;
      }
      else {
         return new Region(surroundingComment.getBeginOffset(),
               surroundingComment.getLength());
      }
   }

   /**
    * Adds style information to the given text presentation. In case of a JML
    * Comment it provides Syntax Highlighting for JML Keywords. If the parser
    * can not find a valid Keyword, the normal Highlighting is used.
    *
    * @param presentation
    *           the text presentation to be extended
    * @param attr
    *           the attribute describing the style of the range to be styled
    * @param surroundingComment
    *           the comment to modify the presentation for
    */
   protected void modifyPresentationForJMLComment(
         final TextPresentation presentation, final TextAttribute attr,
         final CommentRange surroundingComment) {
      if (attr != null) {
         final int style = attr.getStyle();
         final int fontStyle = style & (SWT.ITALIC | SWT.BOLD | SWT.NORMAL);
         final StyleRange styleRange = new StyleRange(
               surroundingComment.getBeginOffset(),
               surroundingComment.getLength(), attr.getForeground(),
               attr.getBackground(), fontStyle);
         styleRange.strikeout = (style & TextAttribute.STRIKETHROUGH) != 0;
         styleRange.underline = (style & TextAttribute.UNDERLINE) != 0;
         styleRange.font = attr.getFont();
         presentation.addStyleRange(styleRange);
         final StyleRange[] highlightedRanges = this.createStylesForJML(
               styleRange, attr, surroundingComment);
         if (highlightedRanges != null) {
            presentation.mergeStyleRanges(highlightedRanges);
         }
      }

   }

   /**
    * Creates an array of StyleRanges to add to the presentation for the JML
    * content.
    *
    * @param defaultStyleRange
    *           the default style range of the comment
    * @param attr
    *           the text attributes of the comment
    * @param surroundingComment
    *           the comment currently working in
    * @return the array of {@link StyleRange}s, may be null
    */
   private StyleRange[] createStylesForJML(final StyleRange defaultStyleRange,
         final TextAttribute attr, final CommentRange surroundingComment) {
      // Can only proceed if a profile is there
      if (!JMLPreferencesHelper.isAnyProfileAvailable()) {
         return null;
      }
      // Parse the comment
      final IJMLProfile activeProfile = JMLPreferencesHelper
            .getProjectActiveJMLProfile(WorkbenchUtil
                  .getProject(this.editorPart));
      final IJMLParser parser = activeProfile.createParser();
      IASTNode parseResult;
      try {
         parseResult = parser.parse(this.doc.get(), surroundingComment);

      }
      catch (final ParserException e) {
         // Invalid JML Code, do syntax coloring with the recovered node
         parseResult = e.getErrorNode();

      }
      if (parseResult == null) {
         // No parser recovery, so no highlightinh
         return null;
      }
      return this.doKeywordHighlighting(defaultStyleRange, attr, parseResult,
            surroundingComment);
   }

   /**
    * This Method creates StyleRanges for Highlighting JML Keywords.
    *
    * @param defaultStyleRange
    *           the default Style Range of the Section to process
    * @param attr
    *           the TextAttribute that is used by default
    * @param parseResult
    *           the IASTNode which has been parsed for the JML Comment. The node
    *           may be a result of parser recovery.
    * @param surroundingComment
    *           the comment range we are currently working in
    * @return a StyleRange Array that has the Styles for all keywords and the
    *         rest which can be merged by the caller. returns null if no profile
    *         is active, the offset is not in a JML Comment or the parse Result
    *         is null
    */
   private StyleRange[] doKeywordHighlighting(
         final StyleRange defaultStyleRange, final TextAttribute attr,
         final IASTNode parseResult, final CommentRange surroundingComment) {
      // Colors for keywords
      final Color toplevelKeywordColor = new Color(Display.getCurrent(),
            JMLUiPreferencesHelper
                  .getWorkspaceJMLColor(ColorProperty.TOPLEVEL_KEYWORD));
      final Color keywordColor = new Color(Display.getCurrent(),
            JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.KEYWORD));

      // List of all keywords and list for a style for each keyword
      final List<IKeywordNode> allKeywords = Nodes.getAllKeywords(parseResult);
      final List<StyleRange> styles = new ArrayList<StyleRange>();

      // Create the styles
      for (final IKeywordNode kNode : allKeywords) {
         // Determine color for keyword
         final Color color;
         if (ToplevelKeywordSort.INSTANCE.covers(kNode.getKeyword().getSort())) {
            color = toplevelKeywordColor;
         }
         else {
            color = keywordColor;
         }
         // Create style in bold for keyword
         final int keywordStartOffset = kNode.getStartOffset();
         final int keywordEndOffset = kNode.getEndOffset();
         styles.add(new StyleRange(keywordStartOffset, keywordEndOffset
               - keywordStartOffset, color, defaultStyleRange.background,
               SWT.BOLD));
      }
      // Transfer to Array
      return styles.toArray(new StyleRange[styles.size()]);
   }

}
