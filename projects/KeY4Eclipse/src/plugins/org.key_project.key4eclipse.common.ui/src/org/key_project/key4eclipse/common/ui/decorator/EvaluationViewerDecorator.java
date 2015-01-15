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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateValue;

/**
 * An extended {@link ProofSourceViewerDecorator} to visualize {@link BranchResult}s
 * via {@link #showSequent(Term, Services, KeYMediator, BranchResult)}.
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
    * @param sequent The {@link Term} to show.
    * @param services The {@link Services} to use.
    * @param mediator The {@link KeYMediator} to use.
    * @param branchResult The {@link BranchResult}s to visualize.
    * @return The shown {@link PredicateValue} of {@link Term} to show.
    */
   public PredicateValue showSequent(Sequent sequent, 
                                     Services services, 
                                     KeYMediator mediator, 
                                     final BranchResult branchResult) {
      // Show Term
      VisibleTermLabels visibleTermLabels = new VisibleTermLabels() {
         @Override
         public boolean contains(Name name) {
            return true; //!ObjectUtil.equals(name, branchResult.getTermLabelName());
         }
      };
      String text = showSequent(sequent, services, mediator, visibleTermLabels);
      // Highlight results of all terms
      LogicPrinter printer = getPrinter();
      InitialPositionTable ipt = printer.getInitialPositionTable();
      List<StyleRange> styleRanges = new LinkedList<StyleRange>();
      PredicateValue sequentValue = fillSequentRanges(sequent, ipt, branchResult, text.length(), styleRanges);
      try {
         TextPresentation textPresentation = createTextPresentation(styleRanges);
         TextPresentation.applyTextPresentation(textPresentation, getViewerText());
         getViewer().changeTextPresentation(textPresentation, true);
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
      // Return term result
      return sequentValue != null ? sequentValue : PredicateValue.UNKNOWN;
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
    * Utility method used by {@link #showSequent(Term, Services, KeYMediator, BranchResult)}
    * to fill the {@link TextPresentation} to highlight {@link PredicateValue}s recursively.
    * @param sequent The current {@link Sequent}.
    * @param positionTable The {@link InitialPositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @return The {@link PredicateValue} of the {@link Sequent}.
    */
   protected PredicateValue fillSequentRanges(Sequent sequent, 
                                              InitialPositionTable positionTable, 
                                              BranchResult branchResult,
                                              int textLength,
                                              List<StyleRange> styleRanges) {
      Map<Term, PredicateValue> termValueMap = new HashMap<Term, PredicateValue>();
      ImmutableList<Integer> path = ImmutableSLList.<Integer>nil().prepend(0); // Sequent arrow
      // Evaluate antecedent
      int i = 0;
      PredicateValue antecedentValue = PredicateValue.TRUE;
      for (SequentFormula sf : sequent.antecedent()) {
         fillTermRanges(sf.formula(), positionTable, branchResult, textLength, termValueMap, path.append(i), styleRanges);
         antecedentValue = PredicateValue.and(antecedentValue, termValueMap.get(sf.formula()));
         i++;
      }
      // Evaluate succedent
      PredicateValue succedentValue = PredicateValue.FALSE;
      for (SequentFormula sf : sequent.succedent()) {
         fillTermRanges(sf.formula(), positionTable, branchResult, textLength, termValueMap, path.append(i), styleRanges);
         succedentValue = PredicateValue.or(succedentValue, termValueMap.get(sf.formula()));
         i++;
      }
      // Evaluate sequent
      int antecedentEnd = positionTable.rangeForPath(path.append(sequent.antecedent().size() - 1), textLength).end();
      int succedentStart = positionTable.rangeForPath(path.append(sequent.antecedent().size()), textLength).start();
      PredicateValue sequentValue = PredicateValue.imp(antecedentValue, succedentValue);
      Color color = getColor(sequentValue);
      StyleRange styleRange = new StyleRange(antecedentEnd, succedentStart - antecedentEnd, color, null);
      styleRanges.add(styleRange);
      return sequentValue;
   }

   /**
    * Utility method used by {@link #showSequent(Term, Services, KeYMediator, BranchResult)}
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
      PredicateTermLabel label = branchResult.getPredicateLabel(term);
      if (PredicateEvaluationUtil.isIfThenElseFormula(term)) {
         fillIfThenElse(term, positionTable, branchResult, textLength, termValueMap, path, styleRanges, label);
      }
      else if (term.op() instanceof Junctor || term.op() == Equality.EQV) {
         // Junctors are supported.
         Operator operator = term.op();
         if (operator.arity() > 2) {
            throw new RuntimeException("Junctors with arity > 2 are not supported.");
         }
         else if (operator.arity() == 2) {
            fillArity2(term, positionTable, branchResult, textLength, termValueMap, path, styleRanges, operator, label);
         }
         else if (operator.arity() == 1) {
            fillArity1(term, positionTable, branchResult, textLength, termValueMap, path, styleRanges, operator, label);
         }
         else if (operator.arity() == 0) {
            fillArity0(term, positionTable, branchResult, textLength, termValueMap, path, styleRanges, operator);
         }
      }
      else if (label != null) {
         // The BranchResult knows the result of the current Term.
         PredicateResult predicateResult = branchResult.evaluate(label);
         PredicateValue value = predicateResult != null ? predicateResult.getValue() : PredicateValue.UNKNOWN;
         Color color = getColor(value);
         Range range = positionTable.rangeForPath(path, textLength);
         StyleRange styleRange = new StyleRange(range.start(), range.length(), color, null);
         termValueMap.put(term, value);
         styleRanges.add(styleRange);
      }
   }
   
   /**
    * Utility method used by {@link #fillTermRanges(Term, PositionTable, BranchResult, int, Map, ImmutableList, List)}
    * to deal with {@code if-then-else} formulas.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link PredicateValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param label The {@link PredicateTermLabel} of the current {@link Term} or {@code null} if {@link Term} is not labeled.
    */
   protected void fillIfThenElse(Term term, 
                                 PositionTable positionTable, 
                                 BranchResult branchResult,
                                 int textLength,
                                 Map<Term, PredicateValue> termValueMap,
                                 ImmutableList<Integer> path,
                                 List<StyleRange> styleRanges,
                                 PredicateTermLabel label) {
      Term conditionTerm = term.sub(0);
      Term thenTerm = term.sub(1);
      Term elseTerm = term.sub(2);
      fillTermRanges(conditionTerm, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      fillTermRanges(thenTerm, positionTable, branchResult, textLength, termValueMap, path.append(1), styleRanges);
      fillTermRanges(elseTerm, positionTable, branchResult, textLength, termValueMap, path.append(2), styleRanges);
      PredicateValue conditionValue = termValueMap.get(conditionTerm);
      PredicateValue thenValue = termValueMap.get(thenTerm);
      PredicateValue elseValue = termValueMap.get(elseTerm);
      PredicateValue operatorResult;
      if (label != null) {
         PredicateResult predicateResult = branchResult.evaluate(label);
         operatorResult = (predicateResult != null ? predicateResult.getValue() : PredicateValue.UNKNOWN);
      }
      else {
         operatorResult = PredicateValue.ifThenElse(conditionValue, thenValue, elseValue);
      }
      // Style range for if
      Color color = getColor(operatorResult);
      Range termRange = positionTable.rangeForPath(path, textLength);
      Range conditionRange = positionTable.rangeForPath(path.append(0), textLength);
      StyleRange styleRange = new StyleRange(termRange.start(), 
                                             conditionRange.start() - termRange.start(), 
                                             color, 
                                             null);
      termValueMap.put(term, operatorResult);
      styleRanges.add(styleRange);
      // Style range for then
      Range thenRange = positionTable.rangeForPath(path.append(1), textLength);
      StyleRange thenStyleRange = new StyleRange(conditionRange.end(), 
                                                 thenRange.start() - conditionRange.end(), 
                                                 color, 
                                                 null);
      styleRanges.add(thenStyleRange);
      // Style range for additional space on the left (e.g. closing brackets)
      Range elseRange = positionTable.rangeForPath(path.append(2), textLength);
      StyleRange elseStyleRange = new StyleRange(thenRange.end(), 
                                                 elseRange.start() - thenRange.end(), 
                                                 color, 
                                                 null);
      styleRanges.add(elseStyleRange);
      // Closing brackets
      if (termRange.end() > elseRange.end()) {
         StyleRange closingStyleRange = new StyleRange(elseRange.end(), 
                                                       termRange.end() - elseRange.end(), 
                                                       color, 
                                                       null);
         styleRanges.add(closingStyleRange);
      }
   }
   
   /**
    * Utility method used by {@link #fillTermRanges(Term, PositionTable, BranchResult, int, Map, ImmutableList, List)}
    * to deal with logical operators of arity {@code 2}.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link PredicateValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param operator The {@link Operator} of the current {@link Term}.
    * @param label The {@link PredicateTermLabel} of the current {@link Term} or {@code null} if {@link Term} is not labeled.
    */
   protected void fillArity2(Term term, 
                             PositionTable positionTable, 
                             BranchResult branchResult,
                             int textLength,
                             Map<Term, PredicateValue> termValueMap,
                             ImmutableList<Integer> path,
                             List<StyleRange> styleRanges,
                             Operator operator,
                             PredicateTermLabel label) {
      Term sub0 = term.sub(0);
      Term sub1 = term.sub(1);
      fillTermRanges(sub0, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      fillTermRanges(sub1, positionTable, branchResult, textLength, termValueMap, path.append(1), styleRanges);
      PredicateValue leftValue = termValueMap.get(sub0);
      PredicateValue rightValue = termValueMap.get(sub1);
      PredicateValue operatorResult = null;
      if (label != null) {
         PredicateResult predicateResult = branchResult.evaluate(label);
         operatorResult = (predicateResult != null ? predicateResult.getValue() : null); // In case of the unknown predicate the result value will be computed because the operatorResult is set to null.
      }
      if (operatorResult == null) {
         if (operator == Junctor.AND) {
            operatorResult = PredicateValue.and(leftValue, rightValue);
         }
         else if (operator == Junctor.IMP) {
            operatorResult = PredicateValue.imp(leftValue, rightValue);
         }
         else if (operator == Junctor.OR) {
            operatorResult = PredicateValue.or(leftValue, rightValue);
         }
         else if (operator == Equality.EQV) {
            operatorResult = PredicateValue.eqv(leftValue, rightValue);
         }
         else {
            throw new RuntimeException("Operator '" + operator + "' is not supported.");
         }
      }
      // Style range for operator
      Color color = getColor(operatorResult);
      Range leftChildRange = positionTable.rangeForPath(path.append(0), textLength);
      Range rightChildRange = positionTable.rangeForPath(path.append(1), textLength);
      StyleRange styleRange = new StyleRange(leftChildRange.end(), 
                                             rightChildRange.start() - leftChildRange.end(), 
                                             color, 
                                             null);
      termValueMap.put(term, operatorResult);
      styleRanges.add(styleRange);
      // Style range for additional space on the left (e.g. opening brackets)
      Range operatorRange = positionTable.rangeForPath(path, textLength);
      if (operatorRange.start() < leftChildRange.start()) {
         StyleRange leftStyleRange = new StyleRange(operatorRange.start(), 
                                                    leftChildRange.start() - operatorRange.start(), 
                                                    color, 
                                                    null);
         styleRanges.add(leftStyleRange);
      }
      // Style range for additional space on the left (e.g. closing brackets)
      if (operatorRange.end() > rightChildRange.end()) {
         StyleRange leftStyleRange = new StyleRange(rightChildRange.end(), 
                                                    operatorRange.end() - rightChildRange.end(), 
                                                    color, 
                                                    null);
         styleRanges.add(leftStyleRange);
      }
   }
   
   /**
    * Utility method used by {@link #fillTermRanges(Term, PositionTable, BranchResult, int, Map, ImmutableList, List)}
    * to deal with logical operators of arity {@code 1}.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link PredicateValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param operator The {@link Operator} of the current {@link Term}.
    * @param label The {@link PredicateTermLabel} of the current {@link Term} or {@code null} if {@link Term} is not labeled.
    */
   protected void fillArity1(Term term, 
                             PositionTable positionTable, 
                             BranchResult branchResult,
                             int textLength,
                             Map<Term, PredicateValue> termValueMap,
                             ImmutableList<Integer> path,
                             List<StyleRange> styleRanges,
                             Operator operator,
                             PredicateTermLabel label) {
      Term sub = term.sub(0);
      fillTermRanges(sub, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      PredicateValue childValue = termValueMap.get(sub);
      PredicateValue junctorResult;
      if (label != null) {
         PredicateResult predicateResult = branchResult.evaluate(label);
         junctorResult = (predicateResult != null ? predicateResult.getValue() : PredicateValue.UNKNOWN);
      }
      else {
         if (operator == Junctor.NOT) {
            junctorResult = PredicateValue.not(childValue);
         }
         else {
            throw new RuntimeException("Junctor '" + operator + "' is not supported.");
         }
      }
      Color color = getColor(junctorResult);
      Range range = positionTable.rangeForPath(path, textLength);
      Range childRange = positionTable.rangeForPath(path.append(0), textLength);
      StyleRange startStyleRange = new StyleRange(range.start(), 
                                             childRange.start() - range.start(), 
                                             color, 
                                             null);
      termValueMap.put(term, junctorResult);
      styleRanges.add(startStyleRange);
      if (childRange.end() < range.end()) {
         StyleRange endStyleRange = new StyleRange(childRange.end(), 
                                                   range.end() - childRange.end(), 
                                                   color, 
                                                   null);
         styleRanges.add(endStyleRange);
      }
   }
   
   /**
    * Utility method used by {@link #fillTermRanges(Term, PositionTable, BranchResult, int, Map, ImmutableList, List)}
    * to deal with logical operators of arity {@code 0}.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link PredicateValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param operator The {@link Operator} of the current {@link Term}.
    */
   protected void fillArity0(Term term, 
                             PositionTable positionTable, 
                             BranchResult branchResult,
                             int textLength,
                             Map<Term, PredicateValue> termValueMap,
                             ImmutableList<Integer> path,
                             List<StyleRange> styleRanges,
                             Operator operator) {
      PredicateValue value;
      if (operator == Junctor.TRUE) {
         value = PredicateValue.TRUE;
      }
      else if (operator == Junctor.FALSE) {
         value = PredicateValue.FALSE;
      }
      else {
         throw new RuntimeException("Junctor '" + operator + "' is not supported.");
      }
      Color color = getColor(value);
      Range range = positionTable.rangeForPath(path, textLength);
      StyleRange styleRange = new StyleRange(range.start(), range.length(), color, null);
      termValueMap.put(term, value);
      styleRanges.add(styleRange);
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
