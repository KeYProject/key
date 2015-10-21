package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.math3.distribution.NormalDistribution;
import org.apache.commons.math3.stat.inference.TestUtils;
import org.apache.commons.math3.stat.inference.WilcoxonSignedRankTest;
import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.sed.key.evaluation.server.util.StatisticsUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * Appends the hypotheses tests.
 * @author Martin Hentschel
 */
public class HTMLHypotheses implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public void appendSection(File storageLocation, 
                             AbstractEvaluation evaluation, 
                             EvaluationResult result, 
                             Statistics statistics, 
                             StringBuffer sb) {
      // Collect data for hypotheses test
      Map<IStatisticsFilter, HypothesisData> dataMap = computeHypothesisData(result, statistics);
      // Append hypotheses test
      sb.append("<h1><a name=\"hypotheses\">Hypotheses</a></h1>");
      for (Entry<IStatisticsFilter, HypothesisData> entry : dataMap.entrySet()) {
         Set<Tool> tools = entry.getValue().getTools();
         sb.append("<h2>" + entry.getKey().getName() + "</h2>");
         // Append hypotheses
         if (tools.size() != 2) {
            throw new IllegalStateException("Exactly two tools are expected, but " + tools.size() + " tools are available.");
         }
         Tool firstTool = evaluation.getTools()[1];
         Tool secondTool = evaluation.getTools()[0];
         HypothesisToolData firstToolData = entry.getValue().getToolData(firstTool);
         HypothesisToolData secondToolData = entry.getValue().getToolData(secondTool);
         double alpha = 0.05;
         appendTest(firstToolData.listCorrectRatios(), 
                    secondToolData.listCorrectRatios(), 
                    alpha, 
                    "Average Correct Answers", 
                    sb);
         sb.append("<br>");
         appendTest(firstToolData.listCorrectnessScoreRatios(), 
                    secondToolData.listCorrectnessScoreRatios(), 
                    alpha, 
                    "Correctness Score", 
                    sb);
         sb.append("<br>");
         appendTest(firstToolData.listNormalizedTrustScoreRatios(), 
                    secondToolData.listNormalizedTrustScoreRatios(), 
                    alpha, 
                    "Trust Score", 
                    sb);
         sb.append("<br>");
         appendTest(secondToolData.listTimeRatios(), 
                    firstToolData.listTimeRatios(), 
                    alpha, 
                    "Time", 
                    sb);
         sb.append("<br>");
         appendDataSets(entry.getValue(), CollectionUtil.toList(firstTool, secondTool), sb);
      }
   }
   
   /**
    * Performs and appends the test one sided test that firstTool > secondTool.
    * @param firstTool The data of the first tool.
    * @param secondTool The data of the second tool.
    * @param alpha The alpha to use.
    * @param hypotheses The tested hypotheses.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendTest(double[] firstTool, 
                             double[] secondTool, 
                             double alpha, 
                             String hypotheses, 
                             StringBuffer sb) {
      // Perform t Test, see https://commons.apache.org/proper/commons-math/userguide/stat.html
      Exception tException = null;
      double pairedT = 0.0;
      double pairedTTest = 0.0;
      boolean pairedTTestAlpha = false;
      try {
         pairedT = TestUtils.pairedT(firstTool, secondTool);
         pairedTTest = TestUtils.pairedTTest(firstTool, secondTool);
         pairedTTestAlpha = TestUtils.pairedTTest(firstTool, secondTool, alpha * 2);
      }
      catch (Exception e) {
         tException = e;
      }
      // Perform ChiSquare Test
      long[] histogram = null;
      double[] expected = null;
      Exception chiSquareException = null;
      double chiSquare = 0.0;
      double chiSquareTest = 0.0;
      boolean chiSquareTestAlpha = false;
      try {
         double[] allData = new double[firstTool.length + secondTool.length];
         System.arraycopy(firstTool, 0, allData, 0, firstTool.length);
         System.arraycopy(secondTool, 0, allData, firstTool.length, secondTool.length);
         histogram = StatisticsUtil.computeNormalDistributionHistogram(allData);
         final NormalDistribution unitNormal = new NormalDistribution(10d, 1d);
         expected = unitNormal.sample(histogram.length);
         chiSquare = TestUtils.chiSquare(expected, histogram);
         chiSquareTest = TestUtils.chiSquareTest(expected, histogram);
         chiSquareTestAlpha = TestUtils.chiSquareTest(expected, histogram, alpha);
      }
      catch (Exception e) {
         chiSquareException = e;
      }
      // Perform sign test
      double signTest = 0.0;
      boolean signTestAlpha = false;
      Exception signTestException = null;
      try {
         signTest = StatisticsUtil.signTest(secondTool, firstTool);
         signTestAlpha = StatisticsUtil.signTest(secondTool, firstTool, alpha, false);
      }
      catch (Exception e) {
         signTestException = e;
      }
      // Perform wilcoxon signed rank test
      double wilcoxon = 0.0;
      double wilcoxonTest = 0.0;
      boolean wilcoxonTestAlpha = false;
      Exception wilcoxonException = null;
      try {
         WilcoxonSignedRankTest test = new WilcoxonSignedRankTest();
         wilcoxon = test.wilcoxonSignedRank(firstTool, secondTool);
         wilcoxonTest = test.wilcoxonSignedRankTest(firstTool, secondTool, true);
         wilcoxonTestAlpha = wilcoxonTest < alpha * 2;
      }
      catch (Exception e) {
         wilcoxonException = e;
      }
      // Extend HTML report
      sb.append("<table border=\"1\">");
      sb.append("<tr>");
      sb.append("<td colspan=\"5\" align=\"center\"><b>" + hypotheses + "</b></td>");
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append("<td>&nbsp;</td>");
      sb.append("<td><b>Paired T-Test (one-sided)</b></td>");
      sb.append("<td><b>ChiSquare Goodness of fit Test for Normal Distribution</b></td>");
      sb.append("<td><b>Wilcoxon Signed Rank Test</b></td>");
      sb.append("<td><b>Sign Test</b></td>");
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append("<td><b>test statistic</b></td>");
      if (tException == null) {
         sb.append("<td>" + pairedT + "</td>");
      }
      else {
         sb.append("<td rowspan=\"3\">" + tException.getMessage() + "</td>");
      }
      if (chiSquareException == null) {
         sb.append("<td>" + chiSquare + "</td>");
      }
      else {
         sb.append("<td rowspan=\"3\">" + chiSquareException.getMessage() + "</td>");
      }
      if (wilcoxonException == null) {
         sb.append("<td>" + wilcoxon + "</td>");
      }
      else {
         sb.append("<td rowspan=\"3\">" + wilcoxonException.getMessage() + "</td>");
      }
      if (signTestException == null) {
         sb.append("<td>&nbsp;</td>");
      }
      else {
         sb.append("<td rowspan=\"3\">" + signTestException.getMessage() + "</td>");
      }
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append("<td><b>p-value (smallest significance level)</b></td>");
      if (tException == null) {
         sb.append("<td>" + (pairedTTest / 2) + "</td>");
      }
      if (chiSquareException == null) {
         sb.append("<td colspan=\"1\">" + chiSquareTest + "</td>");
      }
      if (wilcoxonException == null) {
         sb.append("<td colspan=\"1\">" + (wilcoxonTest / 2) + "</td>");
      }
      if (signTestException == null) {
         sb.append("<td colspan=\"1\">" + signTest + "</td>");
      }
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append("<td><b>sigTest(" + alpha + ")</b></td>");
      if (tException == null) {
         sb.append("<td>" + colorBoolean(pairedTTestAlpha) + "</td>");
      }
      if (chiSquareException == null) {
         sb.append("<td colspan=\"1\">" + colorBoolean(chiSquareTestAlpha) + "</td>");
      }
      if (wilcoxonException == null) {
         sb.append("<td colspan=\"1\">" + colorBoolean(wilcoxonTestAlpha) + "</td>");
      }
      if (signTestException == null) {
         sb.append("<td colspan=\"1\">" + colorBoolean(signTestAlpha) + "</td>");
      }
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append("</table>");
   }
   
   /**
    * Colors the given value.
    * @param value The value to color.
    * @return The colored HTML string.
    */
   protected String colorBoolean(boolean value) {
      return value ?
             "<font color=\"darkgreen\">" + value + "</font>" :
             "<font color=\"red\">" + value + "</font>";
   }
   
   /**
    * Appends the data set.
    * @param data The {@link HypothesisData} to append.
    * @param tools The available {@link Tool}s.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendDataSets(HypothesisData data, List<Tool> tools, StringBuffer sb) {
      sb.append("<table border=\"1\">");
      sb.append("<tr>");
      sb.append("<td><b>Tool</b></td>");
      sb.append("<td><b>UUID</b></td>");
      sb.append("<td><b>Correct</b></td>");
      sb.append("<td><b>Maximal Correct</b></td>");
      sb.append("<td><b>Correct Ratio</b></td>");
      sb.append("<td><b>Correctness Score</b></td>");
      sb.append("<td><b>Maximal Correctness Score</b></td>");
      sb.append("<td><b>Correctness Score Ratio</b></td>");
      sb.append("<td><b>Normalized Trust Score</b></td>");
      sb.append("<td><b>Maximal Normalized Trust Score</b></td>");
      sb.append("<td><b>Normalized Trust Score Ratio</b></td>");
      sb.append("<td><b>Time</b></td>");
      sb.append("<td><b>Time Ratio</b></td>");
      sb.append("</tr>");
      for (Tool tool : tools) {
         HypothesisToolData toolData = data.getToolData(tool);
         for (ParticipantResultSummary summary : toolData.getSummaries()) {
            sb.append("<tr>");
            sb.append("<td>" + tool.getName() + "</td>");
            sb.append("<td>" + summary.getId() + "</td>");
            sb.append("<td>" + summary.getCorrectCount() + "</td>");
            sb.append("<td>" + summary.getMaxCorrectCount() + "</td>");
            sb.append("<td>" + summary.computeCorrectRatio() + "</td>");
            sb.append("<td>" + summary.getCorrectnessScore() + "</td>");
            sb.append("<td>" + summary.getMaxCorrectnessScore() + "</td>");
            sb.append("<td>" + summary.computeCorrectnessScoreRatio() + "</td>");
            sb.append("<td>" + summary.getNormalizedTrustScore() + "</td>");
            sb.append("<td>" + summary.getMaxNormalizedTrustScore() + "</td>");
            sb.append("<td>" + summary.computeNormalizedTrustScoreRatio() + "</td>");
            sb.append("<td>" + summary.getTime() + "</td>");
            sb.append("<td>" + summary.getTimeRatio() + "</td>");
            sb.append("</tr>");
         }
      }
      sb.append("</table>");
   }
   
   /**
    * Computes the data for the hypothesis test.
    * @param result The {@link EvaluationResult}.
    * @param statistics The {@link Statistics}.
    * @return The computed data.
    */
   protected Map<IStatisticsFilter, HypothesisData> computeHypothesisData(EvaluationResult result, 
                                                                          Statistics statistics) {
      Map<IStatisticsFilter, HypothesisData> dataMap = new HashMap<IStatisticsFilter, HypothesisData>();
      for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
         EvaluationAnswers answer = entry.getValue();
         if (!answer.hasMultipleValues()) {
            for (IStatisticsFilter filter : statistics.getFilters()) {
               if (filter.accept(answer)) {
                  Map<Tool, ParticipantResultSummary> summaryMap = new HashMap<Tool, ParticipantResultSummary>();
                  HypothesisData data = dataMap.get(filter);
                  if (data == null) {
                     data = new HypothesisData();
                     dataMap.put(filter, data);
                  }
                  Map<Tool, BigInteger> toolTimesSum = new HashMap<Tool, BigInteger>();
                  for (AbstractPage page : answer.getPages()) {
                     List<AbstractPageInput<?>> pageInputs = answer.getPageInputs(page);
                     if (!CollectionUtil.isEmpty(pageInputs)) {
                        if (pageInputs.size() > 1) {
                           throw new IllegalStateException("Multiple page inputs found.");
                        }
                        AbstractPageInput<?> pageInput = pageInputs.get(0);
                        if (pageInput.getPage().isToolBased()) {
                           List<Tool> tools = answer.getTools(pageInput.getPage());
                           if (tools != null) {
                              if (tools.size() > 1) {
                                 throw new IllegalStateException("Multiple tools found.");
                              }
                              ParticipantResultSummary summary = summaryMap.get(tools.get(0));
                              if (summary == null) {
                                 summary = new ParticipantResultSummary(entry.getKey());
                                 summaryMap.put(tools.get(0), summary);
                              }
                              analyzePageInput(summary, pageInput);
                              BigInteger toolTime = toolTimesSum.get(tools.get(0));
                              if (toolTime == null) {
                                 toolTime = BigInteger.ZERO;
                              }
                              toolTime = toolTime.add(BigInteger.valueOf(pageInput.getShownTime()));
                              toolTimesSum.put(tools.get(0), toolTime);
                           }
                        }
                     }
                  }
                  BigInteger totalTime = BigInteger.ZERO;
                  for (BigInteger toolTime : toolTimesSum.values()) {
                     totalTime = totalTime.add(toolTime);
                  }
                  for (Entry<Tool, ParticipantResultSummary> summaryEntry : summaryMap.entrySet()) {
                     summaryEntry.getValue().updateTimeRatio(toolTimesSum.get(summaryEntry.getKey()), totalTime);
                     HypothesisToolData toolData = data.getToolData(summaryEntry.getKey());
                     toolData.addSummary(summaryEntry.getValue());
                  }
               }
            }
         }
      }
      return dataMap;
   }
   
   /**
    * Updates the {@link ParticipantResultSummary}.
    * @param summary The {@link ParticipantResultSummary} to update.
    * @param pageInput The {@link AbstractPageInput} to analyze.
    */
   protected void analyzePageInput(ParticipantResultSummary summary, AbstractPageInput<?> pageInput) {
      summary.updateTime(pageInput.getShownTime());
      if (pageInput instanceof QuestionPageInput) {
         QuestionPageInput questionPageInput = (QuestionPageInput) pageInput;
         for (QuestionInput questionInput : questionPageInput.getQuestionInputs()) {
            analyzeQuestionInput(summary, questionInput);
         }
      }
      else {
         throw new IllegalStateException("Unsupported page input: " + pageInput);
      }
   }
   
   /**
    * Updates the {@link ParticipantResultSummary}.
    * @param summary The {@link ParticipantResultSummary} to update.
    * @param questionInput The {@link QuestionInput} to analyze.
    */
   protected void analyzeQuestionInput(ParticipantResultSummary summary, QuestionInput questionInput) {
      // Update achieved values
      if (questionInput.getValue() != null) {
         summary.update(questionInput.checkCorrectness(), 
                        questionInput.computeCorrectnessScore(),
                        questionInput.computeTrustScore());
         
      }
      // Update maximal values
      if (questionInput.getQuestion() instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) questionInput.getQuestion();
         Set<Choice> correctChoices = choiceQuestion.getCorrectChoices();
         if (!CollectionUtil.isEmpty(correctChoices)) {
            summary.updateMaximal(correctChoices.size());
         }
      }
      // Handle child questions
      for (Choice choice : questionInput.getChoices()) {
         QuestionInput[] choiceInputs = questionInput.getChoiceInputs(choice);
         if (!ArrayUtil.isEmpty(choiceInputs)) {
            for (QuestionInput choiceInput : choiceInputs) {
               analyzeQuestionInput(summary, choiceInput);
            }
         }
      }
      if (questionInput.countChildInputs() > 0) {
         for (QuestionInput childInput : questionInput.getChildInputs()) {
            analyzeQuestionInput(summary, childInput);
         }
      }
   }
   
   private static class HypothesisData {
      private final Map<Tool, HypothesisToolData> toolMap = new HashMap<Tool, HypothesisToolData>();
      
      public HypothesisToolData getToolData(Tool tool) {
         HypothesisToolData result = toolMap.get(tool);
         if (result == null) {
            result = new HypothesisToolData();
            toolMap.put(tool, result);
         }
         return result;
      }
      
      public Set<Tool> getTools() {
         return toolMap.keySet();
      }
   }
   
   private static class HypothesisToolData {
      private final List<ParticipantResultSummary> participantResults = new LinkedList<ParticipantResultSummary>();

      public void addSummary(ParticipantResultSummary summary) {
         participantResults.add(summary);
      }

      public Iterable<ParticipantResultSummary> getSummaries() {
         return participantResults;
      }
      
      public double[] listCorrectRatios() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.computeCorrectRatio().doubleValue();
            i++;
         }
         return result;
      }
      
      public double[] listCorrectnessScoreRatios() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.computeCorrectnessScoreRatio().doubleValue();
            i++;
         }
         return result;
      }
      
      public double[] listNormalizedTrustScoreRatios() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.computeNormalizedTrustScoreRatio().doubleValue();
            i++;
         }
         return result;
      }
      
      public double[] listTimeRatios() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.getTimeRatio().doubleValue();
            i++;
         }
         return result;
      }
   }
   
   private static class ParticipantResultSummary {
      private final String id;
      private BigInteger correctCount = BigInteger.ZERO;
      private BigInteger maxCorrectCount = BigInteger.ZERO;
      private BigInteger correctnessScore = BigInteger.ZERO;
      private BigInteger maxCorrectnessScore = BigInteger.ZERO;
      private BigInteger normalizedTrustScore = BigInteger.ZERO;
      private BigInteger time = BigInteger.ZERO;
      private BigDecimal timeRatio;

      public ParticipantResultSummary(String id) {
         this.id = id;
      }

      public void updateTime(long shownTime) {
         this.time = this.time.add(BigInteger.valueOf(shownTime));
      }
      
      public void updateTimeRatio(BigInteger toolTime, BigInteger totalTime) {
         timeRatio = new BigDecimal(toolTime).divide(new BigDecimal(totalTime), 6, RoundingMode.HALF_EVEN);
      }

      public void update(Boolean correct, Integer correctnessScore, Integer trustScore) {
         if (correct != null) {
            if (correct.booleanValue()) {
               correctCount = correctCount.add(BigInteger.ONE);
            }
         }
         if (correctnessScore != null) {
            this.correctnessScore = this.correctnessScore.add(BigInteger.valueOf(correctnessScore.longValue()));
         }
         if (trustScore != null) {
            this.normalizedTrustScore = this.normalizedTrustScore.add(BigInteger.valueOf(QuestionInput.normalizeTrust(trustScore.intValue())));
         }
      }

      public void updateMaximal(int maxCorrectnessScore) {
         this.maxCorrectCount = this.maxCorrectCount.add(BigInteger.ONE);
         this.maxCorrectnessScore = this.maxCorrectnessScore.add(BigInteger.valueOf(maxCorrectnessScore));
      }

      public String getId() {
         return id;
      }

      public BigInteger getCorrectCount() {
         return correctCount;
      }

      public BigInteger getMaxCorrectCount() {
         return maxCorrectCount;
      }
      
      public BigInteger getCorrectnessScore() {
         return correctnessScore;
      }

      public BigInteger getMaxCorrectnessScore() {
         return maxCorrectnessScore;
      }

      public BigInteger getNormalizedTrustScore() {
         return normalizedTrustScore;
      }

      public BigInteger getMaxNormalizedTrustScore() {
         return maxCorrectCount.multiply(BigInteger.valueOf(4l));
      }

      public BigInteger getTime() {
         return time;
      }

      public BigDecimal getTimeRatio() {
         return timeRatio;
      }

      public BigDecimal computeCorrectRatio() {
         return new BigDecimal(correctCount).divide(new BigDecimal(maxCorrectCount), 2, RoundingMode.HALF_EVEN);
      }

      public BigDecimal computeCorrectnessScoreRatio() {
         return new BigDecimal(correctnessScore).divide(new BigDecimal(maxCorrectnessScore), 2, RoundingMode.HALF_EVEN);
      }

      public BigDecimal computeNormalizedTrustScoreRatio() {
         return new BigDecimal(normalizedTrustScore).divide(new BigDecimal(getMaxNormalizedTrustScore()), 2, RoundingMode.HALF_EVEN);
      }
   }
}
