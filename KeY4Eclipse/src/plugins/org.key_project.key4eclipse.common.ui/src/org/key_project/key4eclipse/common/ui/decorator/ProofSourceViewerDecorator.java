/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.key4eclipse.common.ui.decorator;

import java.util.ArrayList;

import java.util.Collections;
import java.util.Comparator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jface.resource.FontDescriptor;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.JFaceTextUtil;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.bean.Bean;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.nodeviews.HTMLSyntaxHighlighter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

/**
 * The Decorator for the KeYEditor.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofSourceViewerDecorator extends Bean implements IDisposable {
   /**
    * Property {@link #getSelectedPosInSequent()}.
    */
   public static final String PROP_SELECTED_POS_IN_SEQUENT = "selectedPosInSequent";
   
   /**
    * The {@link ISourceViewer} to decorate.
    */
   private final ISourceViewer viewer;
   
   /**
    * The {@link StyledText} provided by {@link #viewer} via {@link ISourceViewer#getTextWidget()}.
    */
   private final StyledText viewerText;
   
   /**
    * The currently shown node.
    */
   private Node node;

   /**
    * The {@link SequentPrintFilter} used to compute the shown text in {@link #viewer}.
    */
   private SequentPrintFilter filter;
   
   /**
    * The {@link LogicPrinter} used to compute the shown text in {@link #viewer}.
    */
   private LogicPrinter printer;
   
   /**
    * The {@link TextPresentation} shown in {@link #viewerText}.
    */
   private TextPresentation textPresentation;
   
   /**
    * The first range used to highlight the selected {@link Term}.
    */
   private StyleRange marked1;
   
   /**
    * The second range used to highlight the selected {@link Term}.
    */
   private StyleRange marked2;
   /**
    * Array of {@link StyleRange} used to highlight Updates.
    */
   private StyleRange[] markedUpdates;
   /**
    * Array of {@link StyleRange} used to highlight keywords.
    */
   private ArrayList<StyleRange> markedKeywords;
   
   /**
    * The {@link StyleRange} to highlight the active statement.
    */
   private StyleRange firstStatementStyleRange;
   
   /**
    * The currently selected {@link PosInSequent}.
    */
   private PosInSequent selectedPosInSequent;
   
   /**
    * {@link Color} used for highlighting text a rule was applied to.
    */
   private Color greenColor = new Color(null, 128, 255, 128);
   /**
    * {@link Color} used for java keywords.
    */
   private Color purpleColor = new Color(null, 127, 0, 85);
   /**
    * {@link Color} used for highlighting KeY keywords.
    */
   private Color blueColor = new Color(null, 0, 0, 192);
   /**
    * {@link Color} used for highlighting updates.
    */
   private Color lightblueColor = new Color(null,167,210,210);
   /**
    * {@link Color} used for highlighting hovering.
    */
   private Color grayColor1 = new Color(null,196,205,226);
   /**
    * {@link Color} used for highlighting hovering.
    */
   private Color grayColor2 = new Color(null,196,205,226);
   /**
    * {@link Color} used for highlighting first statement.
    */
   private Color firstStatementColor = new Color(null, 167,174,192);
   /**
    * {@link FontDescriptor} used to describe boldFont.
    */
   private FontDescriptor descriptor;
   /**
    * {@link Font} used to mark keywords as bold.
    */
   private Font boldFont; 
   /**
    * Java keywords to be highlighted.
    */
   private static final Pattern JAVA_KEYWORDS_PATTERN = 
         Pattern.compile(HTMLSyntaxHighlighter.concat("(", HTMLSyntaxHighlighter.JAVA_KEYWORDS_REGEX, ")"));
   /**
    *  Dynamic logic keywords to be highlighted.
    */
   private static final Pattern DYNAMIC_LOGIC_KEYWORDS_PATTERN = HTMLSyntaxHighlighter.DYNAMIC_LOGIC_KEYWORDS_PATTERN;
   /**
    * Propositional logic keywords to be highlighted.
    */
   private static final Pattern PROP_LOGIC_KEYWORDS_PATTERN = HTMLSyntaxHighlighter.PROP_LOGIC_KEYWORDS_PATTERN;
   /**
    * Propositional logic keywords to be highlighted.
    */
   /**
    * Text shown.
    */
   private String text;
   /**
    * Listens for mouse move events on {@link #viewerText}.
    */
   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         handleMouseMoved(e);
      }
   };

   /**
    * Constructor.
    * @param viewer The {@link ISourceViewer} to decorate.
    */
   public ProofSourceViewerDecorator(ISourceViewer viewer) {
      this.viewer = viewer;
      this.viewerText = viewer.getTextWidget();
      this.viewerText.addMouseMoveListener(mouseMoveListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (viewerText != null && !viewerText.isDisposed()) {
         viewerText.removeMouseMoveListener(mouseMoveListener);
      }
      blueColor.dispose();
      greenColor.dispose();
      purpleColor.dispose();
      lightblueColor.dispose();
      grayColor1.dispose();
      grayColor2.dispose();
      firstStatementColor.dispose();
      boldFont.dispose();
     
   }
   
   /**
    * Shows the given {@link Node} with help of the given {@link KeYMediator}
    * in the decorated {@link ISourceViewer}.
    * @param node The {@link Node} to show.
    * @param mediator The {@link KeYMediator} to use.
    */
   public void showNode(Node node, NotationInfo notationInfo) {
      this.node = node;
      if (node != null) {
         filter = new IdentitySequentPrintFilter(node.sequent());
         printer = new LogicPrinter(new ProgramPrinter(null), 
                                    notationInfo, 
                                    node.proof().getServices());
         text = computeText(notationInfo, node, filter, printer);
      }
      else {
         filter = null;
         printer = null;
         text = "";
      }
      viewer.setDocument(new Document(text));
      // set up StyleRanges for keyword highlighting
      setKeywordHighlights(text);
      
      if (node != null) {
         // if view of current goal is active, highlight all updates
         if (node.getAppliedRuleApp() == null) {
            setBlueBackground(printer.getInitialPositionTable().getUpdateRanges());
            textPresentation = new TextPresentation();
            mergeRanges(textPresentation, false);
         }   
         else {
            PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
            setGreenBackground(pio);
         }
      }
   }
   /**
    * Finds {@link Range} of {@link Term} containing a JavaBlock and fills them into given ArrayList.
    * @param ranges ArrayList to be filled.
    * @param path Path to given {@link Term}.
    * @param term {@link Term} to be searched for {@link Term} containing JavaBlock. 
    * @return ArrayList containing {@link Range} of all {@link Term} containing a JavaBlock.
    */
   private ArrayList<Range> getJavaBlockRanges(ArrayList<Range> ranges, ImmutableList<Integer> path, Term term) {
      if (term.javaBlock() != null && !term.javaBlock().isEmpty()) {
         Range termRange = printer.getInitialPositionTable().rangeForPath(path, text.length());
         // assumption: children of term always come after term 
         int end = termRange.end();
         // subtract ranges of all children of the Term from the range of the Term 
         for (int i = 0; i < term.subs().size(); i++) {
            Range subRange = printer.getInitialPositionTable().rangeForPath(path.append(i), text.length());
            end = end - subRange.length();

         }
         Range javaRange = new Range(termRange.start(), end);
         ranges.add(javaRange);
      }
      // search all children of term for other JavaBlocks
      for (int i = 0; i < term.subs().size(); i++) {
            if (term.sub(i).isContainsJavaBlockRecursive()) {
               getJavaBlockRanges(ranges, path.append(i), term.sub(i));
            }
         }
  
     return ranges;
   }

   /**
    * Sets {@link StyleRange} for keyword highlighting.
    * @param str text to be highlighted
    * @author Anna Filighera
    */
   private void setKeywordHighlights(String str) {
      markedKeywords = new ArrayList<StyleRange>();
      descriptor = FontDescriptor.createFrom(viewer.getTextWidget().getFont()).setStyle(SWT.BOLD); 
      boldFont = descriptor.createFont(viewer.getTextWidget().getDisplay());
      // find java keywords and mark them
      for (int i = 1; i <= node.sequent().size(); i++) {
        Term term = node.sequent().getFormulabyNr(i).formula();
        if (term.isContainsJavaBlockRecursive()) {
           ImmutableList<Integer> path = ImmutableSLList.<Integer>nil().prepend(0);
           Matcher javaMatcher = JAVA_KEYWORDS_PATTERN.matcher(str);
           for (Range range : getJavaBlockRanges(new ArrayList<Range>(), path.append(i - 1), term)) {
              System.out.println("ranges with javablock " + range.toString());
              javaMatcher.region(range.start(), range.end());
              while (javaMatcher.find()) {
                 StyleRange mark = new StyleRange();
                 mark.font = boldFont;
                 mark.foreground = purpleColor;
                 mark.start = javaMatcher.start();
                 mark.length = javaMatcher.end() - javaMatcher.start();
                 markedKeywords.add(mark);              
              }
           } 
        }
      }
      // find KeY keywords and mark them
      Matcher dynamicMatcher = DYNAMIC_LOGIC_KEYWORDS_PATTERN.matcher(str);
      while (dynamicMatcher.find()) {
         StyleRange mark = new StyleRange();
         mark.font = boldFont;
         mark.foreground = blueColor;
         mark.start = dynamicMatcher.start();
         mark.length = dynamicMatcher.end() - dynamicMatcher.start();
       markedKeywords.add(mark);
      }
      Matcher propMatcher = PROP_LOGIC_KEYWORDS_PATTERN.matcher(str);
      while (propMatcher.find()) {
         StyleRange mark = new StyleRange();
         mark.font = boldFont;
         mark.foreground = blueColor;
         mark.start = propMatcher.start();
         mark.length = propMatcher.end() - propMatcher.start();
       markedKeywords.add(mark);
      }
   }
   
   
   /**
    * Shows the given {@link Term} with help of the given {@link KeYMediator}
    * in the decorated {@link ISourceViewer}.
    * @param term The {@link Term} to show.
    * @param services The {@link Services} to use.
    * @param mediator The {@link KeYMediator} to use.
    * @param visibleLabels Optional definition of visible {@link TermLabel}s.
    * @return The shown text.
    */
   public String showSequent(Sequent sequent, 
                             Services services, 
                             NotationInfo notationInfo, 
                             VisibleTermLabels visibleLabels) {
      this.node = null;
      filter = null;
      if (visibleLabels != null) {
         printer = new SequentViewLogicPrinter(new ProgramPrinter(null), 
                                               notationInfo, 
                                               services,
                                               visibleLabels);
      }
      else {
         printer = new LogicPrinter(new ProgramPrinter(null), 
                                    notationInfo, 
                                    services);
      }
      String str = computeText(sequent, printer);
      viewer.setDocument(new Document(str));

      return str;
   }
   
   
   /**
    * Computes the text to show in the {@link KeYEditor}} which consists
    * of the {@link Sequent} including the applied rule.
    * @param sequent The {@link Sequent} to conert into text.
    * @param printer The {@link LogicPrinter} to use.
    * @return The text to show.
    */
   public static String computeText(Sequent sequent, 
                                    LogicPrinter printer) {
      printer.printSequent(sequent);
      String s = printer.toString();
      return StringUtil.trimRight(s);
   }
   
   /**
    * Computes the text to show in the {@link KeYEditor}} which consists
    * of the {@link Sequent} including the applied rule.
    * @param notationInfo The {@link NotationInfo} to use.
    * @param node The {@link Node} to use.
    * @param filter The {@link SequentPrintFilter} to use.
    * @param printer The {@link LogicPrinter} to use.
    * @return The text to show.
    */
   public static String computeText(NotationInfo notationInfo,
                                    Node node, 
                                    SequentPrintFilter filter, 
                                    LogicPrinter printer) {
      
      printer.printSequent(filter);
      String s = printer.toString();
      RuleApp app = node.getAppliedRuleApp();
      s += "\nNode Nr " + node.serialNr() + "\n";
      s += ruleToString(node.proof().getServices(), notationInfo, app, true);
      return s;
   }
   
   public static String ruleToString(Services services, NotationInfo notationInfo, RuleApp app, boolean withHeadder) {
      String s = StringUtil.EMPTY_STRING;
      if ( app != null ) {
         if (withHeadder) {
            s = s + "\n \nUpcoming rule application: \n";
         }
         if (app.rule() instanceof Taclet) {
        LogicPrinter tacPrinter = new LogicPrinter 
            (new ProgramPrinter(null),                        
             notationInfo,
             services,
             true);  
        tacPrinter.printTaclet((Taclet)(app.rule()));    
        s += tacPrinter;
         } else {
           s = s + app.rule();
         }

         if ( app instanceof TacletApp ) {
        TacletApp tapp = (TacletApp)app;
        if ( tapp.instantiations ().getGenericSortInstantiations () !=
             GenericSortInstantiations.EMPTY_INSTANTIATIONS ) {
            s = s + "\n\nWith sorts:\n";
            s = s +
           tapp.instantiations ().getGenericSortInstantiations ();
        }
         }        
     }
      return s;
   }
   /**
    * Sets up {@link StyleRange} for light blue background color.
    * @param ranges Ranges in which blue color should be applied.
    * @author Anna Filighera
    */
   protected void setBlueBackground(final Range[] ranges) {
      markedUpdates = new StyleRange[ranges.length];
      for (int i = 0; i < ranges.length; i++) {
         StyleRange markedUpdate = new StyleRange();
         markedUpdate.background = lightblueColor;
         markedUpdate.start = ranges[i].start();
         markedUpdate.length = ranges[i].end() - ranges[i].start();
         markedUpdates[i] = markedUpdate;
      } 
   }
   
   protected void setGreenBackground(PosInOccurrence pos){
      TextPresentation textPresentation = new TextPresentation();
      marked1 = initializeValuesForBackground(greenColor, textPresentation);
      if (pos != null) {
         ImmutableList<Integer> path = printer.getInitialPositionTable().pathForPosition(pos, filter);
         Range range = printer.getInitialPositionTable().rangeForPath(path);
         marked1.start = range.start();
         marked1.length = range.end()-range.start();
         textPresentation.mergeStyleRanges(markedKeywords.toArray(new StyleRange[markedKeywords.size()]));

         TextPresentation.applyTextPresentation(textPresentation, viewerText);
         viewer.changeTextPresentation(textPresentation, true);
      }
   }

   /**
    * Initializes TextPresentation with colored StyleRange.
    * @param color Background color to be set.
    * @param textPresentation TextPresentation to be initialized.
    * @return mark The colored StyleRange.
    *
    */
   protected StyleRange initializeValuesForBackground(Color color, TextPresentation textPresentation) {
      StyleRange mark = new StyleRange();
      mark.background = color;  
      textPresentation.addStyleRange(mark);
      return mark;
   }

   /**
    * Handles a mouse move event on {@link #viewerText}.
    * @param e The event.
    */
   protected void handleMouseMoved(MouseEvent e) {
      if (node != null) {
         // Update selected PosInSequent
         PosInSequent oldPos = selectedPosInSequent;
         int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
         if (textOffset >= 0) {
            selectedPosInSequent = printer.getInitialPositionTable().getPosInSequent(textOffset, filter);
         }
         else {
            selectedPosInSequent = null;
         }
         // Update shown highlighting if PosInSequent has changed
         if (!ObjectUtil.equals(oldPos, selectedPosInSequent)) {
            // Update highlighting only on goals.
            if (node.getAppliedRuleApp() == null){
               // refresh update and keyword highlighting as range-merging messes with StyleRanges
               setKeywordHighlights(text);
               setBlueBackground(printer.getInitialPositionTable().getUpdateRanges());
               setBackgroundColorForHover();
            }
            // Inform listener
            firePropertyChange(PROP_SELECTED_POS_IN_SEQUENT, oldPos, selectedPosInSequent);
         }
      }
   }

   protected void setBackgroundColorForHover(){
      initializeValuesForHover();
      
      int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
      Range range = printer.getInitialPositionTable().rangeForIndex(textOffset);
      Range firstStatement = printer.getPositionTable().firstStatementRangeForIndex(textOffset);
      
      if(firstStatement != null){
         firstStatementStyleRange.start = firstStatement.start();
         firstStatementStyleRange.length = firstStatement.end()-firstStatement.start();
      
         //start vor first
         if(range.start() < firstStatement.start()){
            //ende vor first 
            if(range.end() < firstStatement.start()){
               marked1.start = range.start();
               marked1.length = range.length();
            }
            //ende in first
            else if(range.end() >= firstStatement.start() && range.end() <= firstStatement.end()){
               marked1.start = range.start();
               marked1.length = (firstStatement.start()) - range.start();
            }
            //ende nach first
            else if(range.end() > firstStatement.end()){
               marked1.start = range.start();
               marked1.length = (firstStatement.start()) - range.start();
               marked2.start = firstStatement.end();
               marked2.length = range.end() - (firstStatement.end());
            }
         }
         //start in first
         else if(range.start() >= firstStatement.start() && range.start() <= firstStatement.end()){
            //ende nach first
            if(range.end() > firstStatement.end()){
               marked1.start = firstStatement.end();
               marked1.length = range.end() - (firstStatement.end());
            }
         }
         //start nach first
         else if(range.start() > firstStatement.end()){
            marked1.start = range.start();
            marked1.length = range.length();
         }
      }
      else {
         marked1.start = range.start();
         marked1.length = range.length(); 
      }
      // merge all StyleRanges
      mergeRanges(textPresentation, true);

   }
   /**
    * Merges all currently present highlighting {@link StyleRange}.
    * @param textPresentation {@link TextPresentation} to which {@link StyleRange} should be added.
    * @param hoverActive Indicates if hovering is active.
    * @author Anna Filighera
    */
   private void mergeRanges(TextPresentation textPresentation, boolean hoverActive) {
      ArrayList<StyleRange> allRanges = new ArrayList<StyleRange>();
      ArrayList<StyleRange> backgroundMarks = new ArrayList<StyleRange>();
      boolean overlaps = false;
      
      if (hoverActive) {
         backgroundMarks.add(firstStatementStyleRange);
         backgroundMarks.add(marked1);
         backgroundMarks.add(marked2);

         // checks for overlapping ranges and adds all conflict free update StyleRanges
         for (StyleRange update : markedUpdates) {
            for (StyleRange hover : backgroundMarks) {
              if (update.start>=hover.start && update.start<=(hover.start+hover.length)) {
                 overlaps = true;
                 break;
               }
            }
            if (!overlaps) {
               backgroundMarks.add(update);
            }
            else {
               overlaps = false;
            }
         }
      }
      // if hovering is not active, overlapping checks are unnecessary
      else {
         for (StyleRange update : markedUpdates) {
            backgroundMarks.add(update);
         }
      }
  
      // handle overlapping ranges
      for (StyleRange keywordRange: markedKeywords) {
         for (StyleRange backgroundRange: backgroundMarks) {
            // checks if keyword bounds overlap with background highlights
            if (keywordRange.start >= backgroundRange.start 
                  && keywordRange.start <= (backgroundRange.start + backgroundRange.length)) {
               overlaps = true;
               // adds keyword with appropriate background color to allRanges
               StyleRange keyword = new StyleRange(keywordRange.start, keywordRange.length, 
                     keywordRange.foreground, backgroundRange.background, SWT.BOLD);
               allRanges.add(keyword);
               // splits background range into two new ranges, which enclose the keyword
               if (keywordRange.start != backgroundRange.start) {
                  StyleRange split = new StyleRange();
                  split.background = backgroundRange.background;
                  split.start = backgroundRange.start;
                  split.length = keywordRange.start - split.start;
                  backgroundMarks.add(split);
               }
               if (keywordRange.start != (backgroundRange.start + backgroundRange.length)) {
                  backgroundRange.length = backgroundRange.start + backgroundRange.length - 
                        (keywordRange.start + keywordRange.length);
                  backgroundRange.start = keywordRange.start + keywordRange.length;
               }
             break;
            }    
         }
         if (!overlaps) {
            allRanges.add(keywordRange);
         }
         else {
            overlaps = false;
         }
      }
     allRanges.addAll(backgroundMarks);
     for (StyleRange range : allRanges) {
        System.out.println(range.toString());
     }
     Collections.sort(allRanges, new RangeComparator());
     textPresentation.mergeStyleRanges(allRanges.toArray(new StyleRange[allRanges.size()]));
     TextPresentation.applyTextPresentation(textPresentation, viewerText);
     viewer.changeTextPresentation(textPresentation, true);
     
   }
   
   protected void initializeValuesForHover(){
      marked1 = new StyleRange();
      marked1.background= grayColor1;
      marked2 = new StyleRange();
      marked2.background= grayColor2;
      firstStatementStyleRange = new StyleRange();
      firstStatementStyleRange.background = firstStatementColor;
      textPresentation = new TextPresentation();
//      textPresentation.addStyleRange(marked1);
//      textPresentation.mergeStyleRange(firstStatementStyleRange);
      viewer.changeTextPresentation(textPresentation, true);
   }

   /**
    * Returns the selected {@link PosInSequent} for the current cursor location.
    * @return The selected {@link PosInSequent} for the current cursor location.
    */
   public PosInSequent getSelectedPosInSequent() {
      return selectedPosInSequent;
   }

   /**
    * Returns the used {@link LogicPrinter}.
    * @return The used {@link LogicPrinter}.
    */
   protected LogicPrinter getPrinter() {
      return printer;
   }

   /**
    * Returns the {@link ISourceViewer} in which this decorator is used.
    * @return The {@link ISourceViewer} in which this decorator is used.
    */
   protected ISourceViewer getViewer() {
      return viewer;
   }

   /**
    * Returns the {@link StyledText} of {@link #getViewer()}.
    * @return The {@link StyledText} of {@link #getViewer()}.
    */
   protected StyledText getViewerText() {
      return viewerText;
   }

   /**
    * Comparator to compare the beginning of {@link StyleRange}.
    * @author Anna Filighera
    *
    */
   public class RangeComparator implements Comparator<StyleRange> {
   @Override
   public int compare(StyleRange o1, StyleRange o2) {
      return o1.start - o2.start;
   } 
   }
}