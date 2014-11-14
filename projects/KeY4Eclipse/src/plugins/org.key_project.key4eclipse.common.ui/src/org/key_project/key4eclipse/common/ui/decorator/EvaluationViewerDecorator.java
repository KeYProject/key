package org.key_project.key4eclipse.common.ui.decorator;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.Range;
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
                                  BranchResult branchResult) {
      // Show Term
      String text = showTerm(term, services, mediator);
      // Highlight results of all terms
      LogicPrinter printer = getPrinter();
      PositionTable pt = printer.getPositionTable();
      TextPresentation textPresentation = new TextPresentation();
      Map<Term, TermHighlighting> highlightings = new HashMap<Term, TermHighlighting>();
      List<StyleRange> lastRanges = fillTermRanges(term, pt, textPresentation, branchResult, text.length(), highlightings, ImmutableSLList.<Integer>nil());
      if (lastRanges != null) {
         for (StyleRange lastRange : lastRanges) {
            textPresentation.addStyleRange(lastRange);
         }
      }
      TextPresentation.applyTextPresentation(textPresentation, getViewerText());
      getViewer().changeTextPresentation(textPresentation, true);
      // Return term result
      TermHighlighting termHighlighting = highlightings.get(term);
      return termHighlighting != null ? termHighlighting.getValue() : PredicateValue.UNKNOWN;
   }
   
   /**
    * Utility method used by {@link #showTerm(Term, Services, KeYMediator, BranchResult)}
    * to fill the {@link TextPresentation} to highlight {@link PredicateValue}s recursively.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param textPresentation The {@link TextPresentation} to fill.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param highlightings The already computed {@link TermHighlighting}s.
    * @param path The path to the current {@link Term}.
    * @return An optional {@link List} of not yet added {@link StyleRange}s in document order still needs to be added to the {@link TextPresentation}.
    */
   protected List<StyleRange> fillTermRanges(Term term, 
                                             PositionTable positionTable, 
                                             TextPresentation textPresentation, 
                                             BranchResult branchResult,
                                             int textLength,
                                             Map<Term, TermHighlighting> highlightings,
                                             ImmutableList<Integer> path) {
      TermLabel label = branchResult.getPredicateLabel(term);
      if (label != null) {
         // The BranchResult knows the result of the current Term.
         PredicateResult predicateResult = branchResult.getResult(label);
         PredicateValue value = predicateResult != null ? predicateResult.getValue() : null;
         Color color = getColor(value);
         Range range = positionTable.rangeForPath(path, textLength);
         StyleRange styleRange = new StyleRange(range.start(), range.length(), color, null);
         highlightings.put(term, new TermHighlighting(value, styleRange.start, styleRange.start + styleRange.length));
         List<StyleRange> lastRanges = new LinkedList<StyleRange>();
         lastRanges.add(styleRange);
         return lastRanges;
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
            List<StyleRange> firstRanges = fillTermRanges(sub0, positionTable, textPresentation, branchResult, textLength, highlightings, path.append(0));
            if (firstRanges != null) {
               List<StyleRange> secondRanges = fillTermRanges(sub1, positionTable, textPresentation, branchResult, textLength, highlightings, path.append(1));
               if (secondRanges != null) {
                  TermHighlighting high0 = highlightings.get(sub0);
                  TermHighlighting high1 = highlightings.get(sub1);
                  assert high0 != null;
                  assert high1 != null;
                  PredicateValue junctorResult;
                  if (junctor == Junctor.AND) {
                     junctorResult = PredicateValue.and(high0.getValue(), high1.getValue());
                  }
                  else if (junctor == Junctor.IMP) {
                     junctorResult = PredicateValue.imp(high0.getValue(), high1.getValue());
                  }
                  else if (junctor == Junctor.OR) {
                     junctorResult = PredicateValue.or(high0.getValue(), high1.getValue());
                  }
                  else {
                     throw new RuntimeException("Junctor '" + junctor + "' is not supported.");
                  }
                  Color color = getColor(junctorResult);
                  StyleRange styleRange = new StyleRange(high0.getEnd(), 
                                                         high1.getStart() - high0.getEnd(), 
                                                         color, 
                                                         null);
                  highlightings.put(term, new TermHighlighting(junctorResult, high0.getStart(), high1.getEnd()));
                  for (StyleRange first: firstRanges) {
                     textPresentation.addStyleRange(first);
                  }
                  textPresentation.addStyleRange(styleRange);
                  return secondRanges;
               }
            }
         }
         else if (junctor.arity() == 1) {
            Term sub = term.sub(0);
            List<StyleRange> subRanges = fillTermRanges(sub, positionTable, textPresentation, branchResult, textLength, highlightings, path.append(0));
            if (subRanges != null) {
               TermHighlighting high = highlightings.get(sub);
               assert high != null;
               PredicateValue junctorResult;
               if (junctor == Junctor.NOT) {
                  junctorResult = PredicateValue.not(high.getValue());
               }
               else {
                  throw new RuntimeException("Junctor '" + junctor + "' is not supported.");
               }
               Color color = getColor(junctorResult);
               Range range = positionTable.rangeForPath(path, textLength);
               StyleRange styleRange = new StyleRange(range.start(), 
                                                      high.getStart() - range.start(), 
                                                      color, 
                                                      null);
               highlightings.put(term, new TermHighlighting(junctorResult, range.start(), high.getEnd()));
               subRanges.add(0, styleRange);
               return subRanges;
            }
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
            highlightings.put(term, new TermHighlighting(value, styleRange.start, styleRange.start + styleRange.length));
            List<StyleRange> lastRanges = new LinkedList<StyleRange>();
            lastRanges.add(styleRange);
            return lastRanges;
         }
      }
      // Term is not supported
      return null;
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
   
   /**
    * Utility class used by {@link EvaluationViewerDecorator#fillTermRanges(Term, PositionTable, TextPresentation, BranchResult, int, Map, ImmutableList)}
    * to represent an already computed {@link Term} highlighting.
    * @author Martin Hentschel
    */
   protected static class TermHighlighting {
      /**
       * The {@link PredicateValue}.
       */
      private final PredicateValue value;
      
      /**
       * The start index.
       */
      private final int start;
      
      /**
       * The end index.
       */
      private final int end;
      
      /**
       * Constructor.
       * @param value The {@link PredicateValue}.
       * @param start The start index.
       * @param end The end index.
       */
      public TermHighlighting(PredicateValue value, int start, int end) {
         this.value = value;
         this.start = start;
         this.end = end;
      }

      /**
       * Returns the {@link PredicateValue}.
       * @return The {@link PredicateValue}.
       */
      public PredicateValue getValue() {
         return value;
      }

      /**
       * Returns the start index.
       * @return The start index.
       */
      public int getStart() {
         return start;
      }

      /**
       * Returns the end index.
       * @return The end index.
       */
      public int getEnd() {
         return end;
      }
   }
}
