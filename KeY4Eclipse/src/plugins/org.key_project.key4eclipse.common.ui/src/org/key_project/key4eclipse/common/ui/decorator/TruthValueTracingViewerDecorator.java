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
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil.TruthValue;

/**
 * An extended {@link ProofSourceViewerDecorator} to visualize {@link BranchResult}s
 * via {@link #showSequent(Term, Services, KeYMediator, BranchResult)}.
 * @author Martin Hentschel
 */
public class TruthValueTracingViewerDecorator extends ProofSourceViewerDecorator {
   /**
    * The {@link Color} to highlight {@link TruthValue#TRUE}.
    */
   private final Color trueColor;

   /**
    * The {@link Color} to highlight {@link TruthValue#FALSE}.
    */
   private final Color falseColor;

   /**
    * The {@link Color} to highlight {@link TruthValue#UNKNOWN} or {@code null}.
    */
   private final Color unknownColor;
   
   /**
    * Constructor.
    * @param viewer The {@link ISourceViewer} to decorate.
    * @param trueRGB The {@link RGB} to highlight true.
    * @param falseRGB The {@link RGB} to highlight false.
    * @param unknownRGB The {@link RGB} to highlight unknown.
    */
   public TruthValueTracingViewerDecorator(ISourceViewer viewer, RGB trueRGB, RGB falseRGB, RGB unknownRGB) {
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
    * @param notationInfo The {@link NotationInfo} to use.
    * @param branchResult The {@link BranchResult}s to visualize.
    * @return The shown {@link TruthValue} of {@link Term} to show.
    */
   public TruthValue showSequent(Sequent sequent, 
                                 Services services, 
                                 NotationInfo notationInfo, 
                                 final BranchResult branchResult) {
      // Show Term
      VisibleTermLabels visibleTermLabels = new VisibleTermLabels() {
         @Override
         public boolean contains(Name name) {
            return !ObjectUtil.equals(name, branchResult.getTermLabelName());
         }
      };
      String text = showSequent(sequent, services, notationInfo, visibleTermLabels);
      // Highlight results of all terms
      LogicPrinter printer = getPrinter();
      InitialPositionTable ipt = printer.getInitialPositionTable();
      List<StyleRange> styleRanges = new LinkedList<StyleRange>();
      TruthValue sequentValue = fillSequentRanges(sequent, ipt, branchResult, text.length(), styleRanges);
      try {
         TextPresentation textPresentation = createTextPresentation(styleRanges);
         TextPresentation.applyTextPresentation(textPresentation, getViewerText());
         getViewer().changeTextPresentation(textPresentation, true);
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
      // Return term result
      return sequentValue != null ? sequentValue : TruthValue.UNKNOWN;
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
    * to fill the {@link TextPresentation} to highlight {@link TruthValue}s recursively.
    * @param sequent The current {@link Sequent}.
    * @param positionTable The {@link InitialPositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @return The {@link TruthValue} of the {@link Sequent}.
    */
   protected TruthValue fillSequentRanges(Sequent sequent, 
                                          InitialPositionTable positionTable, 
                                          BranchResult branchResult,
                                          int textLength,
                                          List<StyleRange> styleRanges) {
      Map<Term, TruthValue> termValueMap = new HashMap<Term, TruthValue>();
      ImmutableList<Integer> path = ImmutableSLList.<Integer>nil().prepend(0); // Sequent arrow
      // Evaluate antecedent
      int i = 0;
      TruthValue antecedentValue = TruthValue.TRUE;
      for (SequentFormula sf : sequent.antecedent()) {
         TruthValue truthValue = fillTermRanges(sf.formula(), positionTable, branchResult, textLength, termValueMap, path.append(i), styleRanges);
         antecedentValue = TruthValue.and(antecedentValue, truthValue);
         i++;
      }
      // Evaluate succedent
      TruthValue succedentValue = TruthValue.FALSE;
      for (SequentFormula sf : sequent.succedent()) {
         TruthValue truthValue = fillTermRanges(sf.formula(), positionTable, branchResult, textLength, termValueMap, path.append(i), styleRanges);
         succedentValue = TruthValue.or(succedentValue, truthValue);
         i++;
      }
      // Evaluate sequent
      int antecedentEnd = positionTable.rangeForPath(path.append(sequent.antecedent().size() - 1), textLength).end();
      int succedentStart = positionTable.rangeForPath(path.append(sequent.antecedent().size()), textLength).start();
      TruthValue sequentValue = TruthValue.imp(antecedentValue, succedentValue);
      Color color = getColor(sequentValue);
      StyleRange styleRange = new StyleRange(antecedentEnd, succedentStart - antecedentEnd, color, null);
      styleRanges.add(styleRange);
      return sequentValue;
   }

   /**
    * Utility method used by {@link #showSequent(Term, Services, KeYMediator, BranchResult)}
    * to fill the {@link TextPresentation} to highlight {@link TruthValue}s recursively.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link TruthValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @return The {@link TruthValue} of the current {@link Term}.
    */
   protected TruthValue fillTermRanges(Term term, 
                                       PositionTable positionTable, 
                                       BranchResult branchResult,
                                       int textLength,
                                       Map<Term, TruthValue> termValueMap,
                                       ImmutableList<Integer> path,
                                       List<StyleRange> styleRanges) {
      if (term.op() instanceof UpdateApplication) {
         // Skip updates
         return fillTermRanges(term.sub(1), positionTable, branchResult, textLength, termValueMap, path.append(1), styleRanges);
      }
      else if (term.op() instanceof Modality) {
         // Skip modality
         return fillTermRanges(term.sub(0), positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      }
      else {
         // Highlight truth values
         FormulaTermLabel label = branchResult.getPredicateLabel(term);
         if (TruthValueTracingUtil.isIfThenElseFormula(term)) {
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
            TruthValue value = branchResult.evaluate(label);
            if (value == null) {
               value = TruthValue.UNKNOWN;
            }
            Color color = getColor(value);
            Range range = positionTable.rangeForPath(path, textLength);
            StyleRange styleRange = new StyleRange(range.start(), range.length(), color, null);
            termValueMap.put(term, value);
            styleRanges.add(styleRange);
         }
         return termValueMap.get(term);
      }
   }
   
   /**
    * Utility method used by {@link #fillTermRanges(Term, PositionTable, BranchResult, int, Map, ImmutableList, List)}
    * to deal with {@code if-then-else} formulas.
    * @param term The current {@link Term}.
    * @param positionTable The {@link PositionTable} to use.
    * @param branchResult The {@link BranchResult} to use.
    * @param textLength The length of the complete text.
    * @param termValueMap The already computed {@link TruthValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param label The {@link FormulaTermLabel} of the current {@link Term} or {@code null} if {@link Term} is not labeled.
    */
   protected void fillIfThenElse(Term term, 
                                 PositionTable positionTable, 
                                 BranchResult branchResult,
                                 int textLength,
                                 Map<Term, TruthValue> termValueMap,
                                 ImmutableList<Integer> path,
                                 List<StyleRange> styleRanges,
                                 FormulaTermLabel label) {
      Term conditionTerm = term.sub(0);
      Term thenTerm = term.sub(1);
      Term elseTerm = term.sub(2);
      fillTermRanges(conditionTerm, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      fillTermRanges(thenTerm, positionTable, branchResult, textLength, termValueMap, path.append(1), styleRanges);
      fillTermRanges(elseTerm, positionTable, branchResult, textLength, termValueMap, path.append(2), styleRanges);
      TruthValue conditionValue = termValueMap.get(conditionTerm);
      TruthValue thenValue = termValueMap.get(thenTerm);
      TruthValue elseValue = termValueMap.get(elseTerm);
      TruthValue operatorResult;
      if (label != null) {
         TruthValue truthValue = branchResult.evaluate(label);
         operatorResult = (truthValue != null ? truthValue : TruthValue.UNKNOWN);
      }
      else {
         operatorResult = TruthValue.ifThenElse(conditionValue, thenValue, elseValue);
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
    * @param termValueMap The already computed {@link TruthValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param operator The {@link Operator} of the current {@link Term}.
    * @param label The {@link FormulaTermLabel} of the current {@link Term} or {@code null} if {@link Term} is not labeled.
    */
   protected void fillArity2(Term term, 
                             PositionTable positionTable, 
                             BranchResult branchResult,
                             int textLength,
                             Map<Term, TruthValue> termValueMap,
                             ImmutableList<Integer> path,
                             List<StyleRange> styleRanges,
                             Operator operator,
                             FormulaTermLabel label) {
      Term sub0 = term.sub(0);
      Term sub1 = term.sub(1);
      fillTermRanges(sub0, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      fillTermRanges(sub1, positionTable, branchResult, textLength, termValueMap, path.append(1), styleRanges);
      TruthValue leftValue = termValueMap.get(sub0);
      TruthValue rightValue = termValueMap.get(sub1);
      TruthValue operatorResult = null;
      if (label != null) {
         TruthValue truthValue = branchResult.evaluate(label);
         operatorResult = (truthValue != null ? truthValue : null); // In case of the unknown value the result value will be computed because the operatorResult is set to null.
      }
      if (operatorResult == null) {
         if (operator == Junctor.AND) {
            operatorResult = TruthValue.and(leftValue, rightValue);
         }
         else if (operator == Junctor.IMP) {
            operatorResult = TruthValue.imp(leftValue, rightValue);
         }
         else if (operator == Junctor.OR) {
            operatorResult = TruthValue.or(leftValue, rightValue);
         }
         else if (operator == Equality.EQV) {
            operatorResult = TruthValue.eqv(leftValue, rightValue);
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
    * @param termValueMap The already computed {@link TruthValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param operator The {@link Operator} of the current {@link Term}.
    * @param label The {@link FormulaTermLabel} of the current {@link Term} or {@code null} if {@link Term} is not labeled.
    */
   protected void fillArity1(Term term, 
                             PositionTable positionTable, 
                             BranchResult branchResult,
                             int textLength,
                             Map<Term, TruthValue> termValueMap,
                             ImmutableList<Integer> path,
                             List<StyleRange> styleRanges,
                             Operator operator,
                             FormulaTermLabel label) {
      Term sub = term.sub(0);
      fillTermRanges(sub, positionTable, branchResult, textLength, termValueMap, path.append(0), styleRanges);
      TruthValue childValue = termValueMap.get(sub);
      TruthValue junctorResult;
      if (label != null) {
         TruthValue truthValue = branchResult.evaluate(label);
         junctorResult = (truthValue != null ? truthValue : TruthValue.UNKNOWN);
      }
      else {
         if (operator == Junctor.NOT) {
            junctorResult = TruthValue.not(childValue);
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
    * @param termValueMap The already computed {@link TruthValue}s.
    * @param path The path to the current {@link Term}.
    * @param styleRanges The {@link List} with found {@link StyleRange}s to fill.
    * @param operator The {@link Operator} of the current {@link Term}.
    */
   protected void fillArity0(Term term, 
                             PositionTable positionTable, 
                             BranchResult branchResult,
                             int textLength,
                             Map<Term, TruthValue> termValueMap,
                             ImmutableList<Integer> path,
                             List<StyleRange> styleRanges,
                             Operator operator) {
      TruthValue value;
      if (operator == Junctor.TRUE) {
         value = TruthValue.TRUE;
      }
      else if (operator == Junctor.FALSE) {
         value = TruthValue.FALSE;
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
    * Returns the {@link Color} of the given {@link TruthValue}.
    * @param value The {@link TruthValue} or {@code null}.
    * @return The {@link Color} to use.
    */
   public Color getColor(TruthValue value) {
      if (TruthValue.TRUE.equals(value)) {
         return trueColor;
      }
      else if (TruthValue.FALSE.equals(value)) {
         return falseColor;
      }
      else {
         return unknownColor;
      }
   }
}
