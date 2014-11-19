package org.key_project.key4eclipse.common.ui.decorator;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateValue;

/**
 * An extended {@link ProofSourceViewerDecorator} to visualize {@link BranchResult}s
 * via {@link #showTerm(Term, Services, KeYMediator, BranchResult)}.
 * @author Martin Hentschel
 */
public class EvaluationViewerDecorator extends ProofSourceViewerDecorator {
   /**
    * The {@link RGB} specifying the {@link Color} to highlight {@link PredicateValue#TRUE}.
    */
   public static final RGB trueRGB = new RGB(0, 117, 0);

   /**
    * The {@link RGB} specifying the {@link Color} to highlight {@link PredicateValue#FALSE}.
    */
   public static final RGB falseRGB = new RGB(170, 0, 0);

   /**
    * The {@link RGB} specifying the {@link Color} to highlight {@link PredicateValue#UNKNOWN} or {@code null}.
    */
   public static final RGB unknownRGB = new RGB(217, 108, 0);
   
   /**
    * The {@link Color} to highlight {@link PredicateValue#TRUE}.
    */
   private final Color trueColor;

   /**
    * The {@link Color} to highlight {@link PredicateValue#FALSE}.
    */
   private final Color falseColor;

   /**
    * The {@link Color} to highlight {@link PredicateValue#UNKNOWN} or {@code null}.
    */
   private final Color unknownColor;
   
   /**
    * Constructor.
    * @param viewer The {@link ISourceViewer} to decorate.
    */
   public EvaluationViewerDecorator(ISourceViewer viewer) {
      super(viewer);
      trueColor = new Color(getViewerText().getDisplay(), trueRGB);
      falseColor = new Color(getViewerText().getDisplay(), falseRGB);
      unknownColor = new Color(getViewerText().getDisplay(), unknownRGB);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (trueColor != null) {
         trueColor.dispose();
      }
      if (falseColor != null) {
         falseColor.dispose();
      }
      if (unknownColor != null) {
         unknownColor.dispose();
      }
      super.dispose();
   }

   /**
    * Shows the given {@link Term} and visualizes the {@link BranchResult}.
    * @param term The {@link Term} to show.
    * @param services The {@link Services} to use.
    * @param mediator The {@link KeYMediator} to use.
    * @param branchResult The {@link BranchResult}s to visualize.
    * @return The shown {@link PredicateValue} of {@link Term} to show.
    */
   public PredicateValue showTerm(Term term, 
                                  Services services, 
                                  KeYMediator mediator, 
                                  final BranchResult branchResult) {
      // Show Term
      VisibleTermLabels visibleTermLabels = new VisibleTermLabels() {
         @Override
         public boolean contains(Name name) {
            return !ObjectUtil.equals(name, branchResult.getTermLabelName());
         }
      };
      String text = showTerm(term, services, mediator, visibleTermLabels);
      // Highlight results of all terms
      LogicPrinter printer = getPrinter();
      PositionTable pt = printer.getPositionTable();
      Map<Term, PredicateValue> termValueMap = new HashMap<Term, PredicateValue>();
      List<StyleRange> styleRanges = new LinkedList<StyleRange>();
      fillTermRanges(term, pt, branchResult, text.length(), termValueMap, ImmutableSLList.<Integer>nil(), styleRanges);
      try {
         TextPresentation textPresentation = createTextPresentation(styleRanges);
         TextPresentation.applyTextPresentation(textPresentation, getViewerText());
         getViewer().changeTextPresentation(textPresentation, true);
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
      // Return term result
      PredicateValue value = termValueMap.get(term);
      return value != null ? value : PredicateValue.UNKNOWN;
   }
   
   /**
    * Creates the {@link TextPresentation} to show.
    * @param styleRanges The {@link StyleRange} to consider.
    * @return The created {@link TextPresentation}.
    */
   private TextPresentation createTextPresentation(List<StyleRange> styleRanges) {
      // Ensure that StyleRanges are in the correct order.
      Collections.sort(styleRanges, new Comparator<StyleRange>() {
         @Override
         public int compare(StyleRange o1, StyleRange o2) {
            return o1.start - o2.start;
         }
      });
      // Create TextPresentation
      TextPresentation textPresentation = new TextPresentation();
      for (StyleRange styleRange : styleRanges) {
         textPresentation.addStyleRange(styleRange);
      }
      return textPresentation;
   }

   /**
    * Utility method used by {@link #showTerm(Term, Services, KeYMediator, BranchResult)}
    * to fill the {@link TextPresentation} to highlight {@link PredicateValue}s recursively.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link PredicateValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    */
   protected void fillTermRanges(Term term, 
                                 PositionTable positionTable, 
                                 BranchResult branchResult,
                                 int textLength,
                                 Map<Term, PredicateValue> termValueMap,
                                 ImmutableList<Integer> path,
                                 List<StyleRange> styleRanges) {
      TermLabel label = branchResult.getPredicateLabel(term);
      if (label != null) {
         // The BranchResult knows the result of the current Term.
         PredicateResult predicateResult = branchResult.getResult(label);
         PredicateValue value = predicateResult != null ? predicateResult.getValue() : PredicateValue.UNKNOWN;
         Color color = getColor(value);
         Range range = positionTable.rangeForPath(path, textLength);
         StyleRange styleRange = new StyleRange(range.start(), range.length(), color, null);
         termValueMap.put(term, value);
         styleRanges.add(styleRange);
      }
      else if (term.op() instanceof Junctor) {
         // Junctors are supported.
         Junctor junctor = (Junctor)term.op();
         if (junctor.arity() > 2) {
            throw new RuntimeException("Junctors with arity > 2 are not supported.");
         }
         else if (junctor.arity() == 2) {
            Term sub0 = term.sub(0);
            Term sub1 = term.sub(1);
            fillTermRanges(sub0, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
            fillTermRanges(sub1, positionTable, branchResult, textLength, termValueMap, path.append(1), styleRanges);
            PredicateValue leftValue = termValueMap.get(sub0);
            PredicateValue rightValue = termValueMap.get(sub1);
            assert leftValue != null;
            assert rightValue != null;
            PredicateValue junctorResult;
            if (junctor == Junctor.AND) {
               junctorResult = PredicateValue.and(leftValue, rightValue);
            }
            else if (junctor == Junctor.IMP) {
               junctorResult = PredicateValue.imp(leftValue, rightValue);
            }
            else if (junctor == Junctor.OR) {
               junctorResult = PredicateValue.or(leftValue, rightValue);
            }
            else {
               throw new RuntimeException("Junctor '" + junctor + "' is not supported.");
            }
            // Style range for operator
            Color color = getColor(junctorResult);
            Range leftChildRange = positionTable.rangeForPath(path.append(0), textLength);
            Range rightChildRange = positionTable.rangeForPath(path.append(1), textLength);
            StyleRange styleRange = new StyleRange(leftChildRange.end(), 
                                                   rightChildRange.start() - leftChildRange.end(), 
                                                   color, 
                                                   null);
            termValueMap.put(term, junctorResult);
            styleRanges.add(styleRange);
            // Style range for additional space on the left (e.g. opening brackets)
            Range junctorRange = positionTable.rangeForPath(path, textLength);
            if (junctorRange.start() < leftChildRange.start()) {
               StyleRange leftStyleRange = new StyleRange(junctorRange.start(), 
                                                          leftChildRange.start() - junctorRange.start(), 
                                                          color, 
                                                          null);
               styleRanges.add(leftStyleRange);
            }
            // Style range for additional space on the left (e.g. closing brackets)
            if (junctorRange.end() > rightChildRange.end()) {
               StyleRange leftStyleRange = new StyleRange(rightChildRange.end(), 
                                                          junctorRange.end() - rightChildRange.end(), 
                                                          color, 
                                                          null);
               styleRanges.add(leftStyleRange);
            }
         }
         else if (junctor.arity() == 1) {
            Term sub = term.sub(0);
            fillTermRanges(sub, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
            PredicateValue childValue = termValueMap.get(sub);
            assert childValue != null;
            PredicateValue junctorResult;
            if (junctor == Junctor.NOT) {
               junctorResult = PredicateValue.not(childValue);
            }
            else {
               throw new RuntimeException("Junctor '" + junctor + "' is not supported.");
            }
            Color color = getColor(junctorResult);
            Range range = positionTable.rangeForPath(path, textLength);
            Range childRange = positionTable.rangeForPath(path.append(0), textLength);
            StyleRange styleRange = new StyleRange(range.start(), 
                                                   childRange.start() - range.start(), 
                                                   color, 
                                                   null);
            termValueMap.put(term, junctorResult);
            styleRanges.add(styleRange);
         }
         else if (junctor.arity() == 0) {
            PredicateValue value;
            if (junctor == Junctor.TRUE) {
               value = PredicateValue.TRUE;
            }
            else if (junctor == Junctor.FALSE) {
               value = PredicateValue.FALSE;
            }
            else {
               throw new RuntimeException("Junctor '" + junctor + "' is not supported.");
            }
            Color color = getColor(value);
            Range range = positionTable.rangeForPath(path, textLength);
            StyleRange styleRange = new StyleRange(range.start(), range.length(), color, null);
            termValueMap.put(term, value);
            styleRanges.add(styleRange);
         }
      }
   }

   /**
    * Returns the {@link Color} of the given {@link PredicateValue}.
    * @param value The {@link PredicateValue} or {@code null}.
    * @return The {@link Color} to use.
    */
   public Color getColor(PredicateValue value) {
      if (PredicateValue.TRUE.equals(value)) {
         return trueColor;
      }
      else if (PredicateValue.FALSE.equals(value)) {
         return falseColor;
      }
      else {
         return unknownColor;
      }
   }
}
