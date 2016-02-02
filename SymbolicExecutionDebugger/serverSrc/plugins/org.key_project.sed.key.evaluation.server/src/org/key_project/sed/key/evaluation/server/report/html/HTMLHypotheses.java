package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.text.DecimalFormat;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.math3.distribution.NormalDistribution;
import org.apache.commons.math3.stat.inference.TestUtils;
import org.apache.commons.math3.stat.inference.WilcoxonSignedRankTest;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.sed.key.evaluation.server.util.LatexUtil;
import org.key_project.sed.key.evaluation.server.util.StatisticsUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Appends the hypotheses tests.
 * @author Martin Hentschel
 */
public class HTMLHypotheses implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, 
                                                   AbstractEvaluation evaluation, 
                                                   EvaluationResult result, 
                                                   Statistics statistics, 
                                                   StringBuffer sb) {
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
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
         TestResultContainer correctAnswers = appendTestAndDiagrams(firstToolData.listCorrectRatios(), 
                               secondToolData.listCorrectRatios(), 
                               alpha, 
                               "Correct Answers", 
                               sb,
                               new String[] {firstTool.getLatexName(), secondTool.getLatexName()},
                               IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + "_CorrectAnswers",
                               additionalFiles,
                               false,
                               0,
                               1);
         sb.append("<br>");
         TestResultContainer correctnessScore = appendTestAndDiagrams(firstToolData.listOverallCorrectnessScoreRatios(), 
                               secondToolData.listOverallCorrectnessScoreRatios(), 
                               alpha, 
                               "Correctness Score", 
                               sb,
                               new String[] {firstTool.getLatexName(), secondTool.getLatexName()},
                               IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + "_CorrectnessScore",
                               additionalFiles,
                               false,
                               0,
                               1);
         sb.append("<br>");
         TestResultContainer trustScore = appendTestAndDiagrams(firstToolData.listTrustScoreRatios(), 
                               secondToolData.listTrustScoreRatios(), 
                               alpha, 
                               "Trust Score", 
                               sb,
                               new String[] {firstTool.getLatexName(), secondTool.getLatexName()},
                               IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + "_TrustScore",
                               additionalFiles,
                               false,
                               -2,
                               2);
         sb.append("<br>");
         TestResultContainer partialTrustScore = appendTestAndDiagrams(firstToolData.listOverallPartialTrustScoreRatio(), 
                               secondToolData.listOverallPartialTrustScoreRatio(), 
                               alpha, 
                               "Partial Trust Score", 
                               sb,
                               new String[] {firstTool.getLatexName(), secondTool.getLatexName()},
                               IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + "_PartialTrustScore",
                               additionalFiles,
                               false,
                               -2,
                               2);
         sb.append("<br>");
         TestResultContainer time = appendTestAndDiagrams(secondToolData.listTimeRatios(), 
                               firstToolData.listTimeRatios(), 
                               alpha, 
                               "Time", 
                               sb,
                               new String[] {secondTool.getLatexName(), firstTool.getLatexName()},
                               IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + "_Time",
                               additionalFiles,
                               true,
                               0,
                               1);
         sb.append("<br>");
         appendDataSets(entry.getValue(), CollectionUtil.toList(firstTool, secondTool), sb);
         // Create paired ttest latex file
         DecimalFormat df = new DecimalFormat("#.####");
         StringBuffer latex = new StringBuffer();
         latex.append("\\begin{tabular}{lrrc}" + StringUtil.NEW_LINE);
         latex.append("\\toprule" + StringUtil.NEW_LINE);
         latex.append("Hypothesis & t-value & p-value & rejected at $\\alpha = $" + alpha + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\midrule" + StringUtil.NEW_LINE);
         latex.append("$H_{0_Q}$ & " + df.format(correctAnswers.getPairedTTest().getTestStatistics()) + " & " + df.format(correctAnswers.getPairedTTest().getpValue()) + " & " + correctAnswers.getPairedTTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_{\\mathit{QS}}}$ & " + df.format(correctnessScore.getPairedTTest().getTestStatistics()) + " & " + df.format(correctnessScore.getPairedTTest().getpValue()) + " & " + correctnessScore.getPairedTTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_C}$ & " + df.format(trustScore.getPairedTTest().getTestStatistics()) + " & " + df.format(trustScore.getPairedTTest().getpValue()) + " & " + trustScore.getPairedTTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_{\\mathit{CS}}}$ & " + df.format(partialTrustScore.getPairedTTest().getTestStatistics()) + " & " + df.format(partialTrustScore.getPairedTTest().getpValue()) + " & " + partialTrustScore.getPairedTTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_T}$ & " + df.format(time.getPairedTTest().getTestStatistics()) + " & " + df.format(time.getPairedTTest().getpValue()) + " & " + time.getPairedTTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\bottomrule" + StringUtil.NEW_LINE);
         latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
         additionalFiles.add(new AdditionalFile("_pairedTTest_" + IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + ".tex", latex.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         // Create ChiSquare Goodness of fit Test latex file
         latex = new StringBuffer();
         latex.append("\\begin{tabular}{lrrc}" + StringUtil.NEW_LINE);
         latex.append("\\toprule" + StringUtil.NEW_LINE);
         latex.append("Data & chi-2-value & p-value & rejected at $\\alpha = $" + alpha + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\midrule" + StringUtil.NEW_LINE);
         latex.append("$\\mu_{Q_{" + firstTool.getLatexName() + "}} \\cup \\mu_{Q_{" + secondTool.getLatexName() + "}}$ & " + df.format(correctAnswers.getChiSquareGoodnessOfFitTest().getTestStatistics()) + " & " + df.format(correctAnswers.getChiSquareGoodnessOfFitTest().getpValue()) + " & " + correctAnswers.getChiSquareGoodnessOfFitTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$\\mu_{\\mathit{QS}_{" + firstTool.getLatexName() + "}} \\cup \\mu_{\\mathit{QS}_{" + secondTool.getLatexName() + "}}$ & " + df.format(correctnessScore.getChiSquareGoodnessOfFitTest().getTestStatistics()) + " & " + df.format(correctnessScore.getChiSquareGoodnessOfFitTest().getpValue()) + " & " + correctnessScore.getChiSquareGoodnessOfFitTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$\\mu_{C_{" + firstTool.getLatexName() + "}} \\cup \\mu_{C_{" + secondTool.getLatexName() + "}}$ & " + df.format(trustScore.getChiSquareGoodnessOfFitTest().getTestStatistics()) + " & " + df.format(trustScore.getChiSquareGoodnessOfFitTest().getpValue()) + " & " + trustScore.getChiSquareGoodnessOfFitTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$\\mu_{\\mathit{CS}_{" + firstTool.getLatexName() + "}} \\cup \\mu_{\\mathit{CS}_{" + secondTool.getLatexName() + "}}$ & " + df.format(partialTrustScore.getChiSquareGoodnessOfFitTest().getTestStatistics()) + " & " + df.format(partialTrustScore.getChiSquareGoodnessOfFitTest().getpValue()) + " & " + partialTrustScore.getChiSquareGoodnessOfFitTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$\\mu_{T_{" + firstTool.getLatexName() + "}} \\cup \\mu_{T_{" + secondTool.getLatexName() + "}}$ & " + df.format(time.getChiSquareGoodnessOfFitTest().getTestStatistics()) + " & " + df.format(time.getChiSquareGoodnessOfFitTest().getpValue()) + " & " + time.getChiSquareGoodnessOfFitTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\bottomrule" + StringUtil.NEW_LINE);
         latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
         additionalFiles.add(new AdditionalFile("_chiSquareGoodnessOfFitTest_" + IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + ".tex", latex.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         // Create Wilcoxon Signed Rank Test latex file
         latex = new StringBuffer();
         latex.append("\\begin{tabular}{lrrc}" + StringUtil.NEW_LINE);
         latex.append("\\toprule" + StringUtil.NEW_LINE);
         latex.append("Hypothesis & W-value & p-value & rejected at $\\alpha = $" + alpha + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\midrule" + StringUtil.NEW_LINE);
         latex.append("$H_{0_Q}$ & " + df.format(correctAnswers.getWilcoxonSignedRankTest().getTestStatistics()) + " & " + df.format(correctAnswers.getWilcoxonSignedRankTest().getpValue()) + " & " + correctAnswers.getWilcoxonSignedRankTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_{\\mathit{QS}}}$ & " + df.format(correctnessScore.getWilcoxonSignedRankTest().getTestStatistics()) + " & " + df.format(correctnessScore.getWilcoxonSignedRankTest().getpValue()) + " & " + correctnessScore.getWilcoxonSignedRankTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_C}$ & " + df.format(trustScore.getWilcoxonSignedRankTest().getTestStatistics()) + " & " + df.format(trustScore.getWilcoxonSignedRankTest().getpValue()) + " & " + trustScore.getWilcoxonSignedRankTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_{\\mathit{CS}}}$ & " + df.format(partialTrustScore.getWilcoxonSignedRankTest().getTestStatistics()) + " & " + df.format(partialTrustScore.getWilcoxonSignedRankTest().getpValue()) + " & " + partialTrustScore.getWilcoxonSignedRankTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_T}$ & " + df.format(time.getWilcoxonSignedRankTest().getTestStatistics()) + " & " + df.format(time.getWilcoxonSignedRankTest().getpValue()) + " & " + time.getWilcoxonSignedRankTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\bottomrule" + StringUtil.NEW_LINE);
         latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
         additionalFiles.add(new AdditionalFile("_wilcoxonSignedRankTest_" + IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + ".tex", latex.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         // Create Sign Test latex file
         latex = new StringBuffer();
         latex.append("\\begin{tabular}{lrc}" + StringUtil.NEW_LINE);
         latex.append("\\toprule" + StringUtil.NEW_LINE);
         latex.append("Hypothesis & p-value & rejected at $\\alpha = $" + alpha + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\midrule" + StringUtil.NEW_LINE);
         latex.append("$H_{0_Q}$ & " + df.format(correctAnswers.getSignTest().getpValue()) + " & " + correctAnswers.getSignTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_{\\mathit{QS}}}$ & " + df.format(correctnessScore.getSignTest().getpValue()) + " & " + correctnessScore.getSignTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_C}$ & " + df.format(trustScore.getSignTest().getpValue()) + " & " + trustScore.getSignTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_{\\mathit{CS}}}$ & " + df.format(partialTrustScore.getSignTest().getpValue()) + " & " + partialTrustScore.getSignTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("$H_{0_T}$ & " + df.format(time.getSignTest().getpValue()) + " & " + time.getSignTest().isRejected() + "\\\\" + StringUtil.NEW_LINE);
         latex.append("\\bottomrule" + StringUtil.NEW_LINE);
         latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
         additionalFiles.add(new AdditionalFile("_signTest_" + IOUtil.validateOSIndependentFileName(entry.getKey().getName()) + ".tex", latex.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      }
      return additionalFiles;
   }
   
   /**
    * Performs and appends the test one sided test that firstTool > secondTool.
    * @param firstTool The data of the first tool.
    * @param secondTool The data of the second tool.
    * @param alpha The alpha to use.
    * @param hypotheses The tested hypotheses.
    * @param sb The {@link StringBuffer} to append to.
    * @return The {@link TestResultContainer} offering all computed results.
    */
   protected TestResultContainer appendTestAndDiagrams(double[] firstTool, 
                                                       double[] secondTool, 
                                                       double alpha, 
                                                       String hypotheses, 
                                                       StringBuffer sb,
                                                       String[] toolLabels,
                                                       String boxplotFileName,
                                                       List<AdditionalFile> additionalFiles,
                                                       boolean reverseOrder,
                                                       int xMin,
                                                       int xMax) {
      // Append test
      TestResultContainer testContainer = appendTest(firstTool, secondTool, alpha, hypotheses, sb);
      // Create latex file with boxplot of data
      String content = LatexUtil.createLatexBoxPlot(new double[][] {firstTool, secondTool}, toolLabels, null, 1.5, reverseOrder, xMin, xMax);
      additionalFiles.add(new AdditionalFile(boxplotFileName + LatexUtil.TEX_FILE_EXTENSION_WITH_DOT, content.getBytes(IOUtil.DEFAULT_CHARSET)));
      return testContainer;
   }
   
   /**
    * Performs and appends the test one sided test that firstTool > secondTool.
    * @param firstTool The data of the first tool.
    * @param secondTool The data of the second tool.
    * @param alpha The alpha to use.
    * @param hypotheses The tested hypotheses.
    * @param sb The {@link StringBuffer} to append to.
    * @return The {@link TestResultContainer} offering all computed results.
    */
   protected TestResultContainer appendTest(double[] firstTool, 
                                            double[] secondTool, 
                                            double alpha, 
                                            String hypotheses, 
                                            StringBuffer sb) {
      // Perform t Test, see https://commons.apache.org/proper/commons-math/userguide/stat.html
      Exception tException = null;
      double pairedT = Double.NaN;
      double pairedTTest = Double.NaN;
      boolean pairedTTestAlpha = false;
      try {
         pairedT = TestUtils.pairedT(firstTool, secondTool);
         pairedTTest = TestUtils.pairedTTest(firstTool, secondTool) / 2;
         pairedTTestAlpha = TestUtils.pairedTTest(firstTool, secondTool, alpha * 2);
      }
      catch (Exception e) {
         tException = e;
      }
      // Perform ChiSquare Test
      long[] histogram = null;
      double[] expected = null;
      Exception chiSquareException = null;
      double chiSquare = Double.NaN;
      double chiSquareTest = Double.NaN;
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
      double signTest = Double.NaN;
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
      double wilcoxon = Double.NaN;
      double wilcoxonTest = Double.NaN;
      boolean wilcoxonTestAlpha = false;
      Exception wilcoxonException = null;
      try {
         WilcoxonSignedRankTest test = new WilcoxonSignedRankTest();
         wilcoxon = test.wilcoxonSignedRank(firstTool, secondTool);
         wilcoxonTest = test.wilcoxonSignedRankTest(firstTool, secondTool, true);
         wilcoxonTestAlpha = wilcoxonTest < alpha * 2;
         wilcoxonTest = wilcoxonTest / 2;
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
         sb.append("<td>" + pairedTTest + "</td>");
      }
      if (chiSquareException == null) {
         sb.append("<td colspan=\"1\">" + chiSquareTest + "</td>");
      }
      if (wilcoxonException == null) {
         sb.append("<td colspan=\"1\">" + wilcoxonTest + "</td>");
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
      return new TestResultContainer(new TestResult(pairedT, pairedTTest, pairedTTestAlpha), // pairedTTest, 
                                     new TestResult(chiSquare, chiSquareTest, chiSquareTestAlpha), //chiSquareGoodnessOfFitTest, 
                                     new TestResult(wilcoxon, wilcoxonTest, wilcoxonTestAlpha), // wilcoxonSignedRankTest, 
                                     new TestResult(Double.NaN, signTest, signTestAlpha)  /* signTest */);
   }
   
   private static class TestResultContainer {
      private final TestResult pairedTTest;
      private final TestResult chiSquareGoodnessOfFitTest;
      private final TestResult wilcoxonSignedRankTest;
      private final TestResult signTest;
      
      public TestResultContainer(TestResult pairedTTest, 
                                 TestResult chiSquareGoodnessOfFitTest, 
                                 TestResult wilcoxonSignedRankTest, 
                                 TestResult signTest) {
         super();
         this.pairedTTest = pairedTTest;
         this.chiSquareGoodnessOfFitTest = chiSquareGoodnessOfFitTest;
         this.wilcoxonSignedRankTest = wilcoxonSignedRankTest;
         this.signTest = signTest;
      }

      public TestResult getPairedTTest() {
         return pairedTTest;
      }

      public TestResult getChiSquareGoodnessOfFitTest() {
         return chiSquareGoodnessOfFitTest;
      }

      public TestResult getWilcoxonSignedRankTest() {
         return wilcoxonSignedRankTest;
      }

      public TestResult getSignTest() {
         return signTest;
      }
   }
   
   private static class TestResult {
      private final double testStatistics;
      
      private final double pValue;
      
      private final boolean rejected;

      public TestResult(double testStatistics, double pValue, boolean rejected) {
         this.testStatistics = testStatistics;
         this.pValue = pValue;
         this.rejected = rejected;
      }

      public double getTestStatistics() {
         return testStatistics;
      }

      public double getpValue() {
         return pValue;
      }

      public boolean isRejected() {
         return rejected;
      }
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
      sb.append("<td><b>Overall Correctness Score Ratio</b></td>");
      sb.append("<td><b>Trust Score Sum</b></td>");
      sb.append("<td><b>Trust Score Count</b></td>");
      sb.append("<td><b>Trust Score Ratio</b></td>");
      sb.append("<td><b>Overall Partial Trust Score Ratio</b></td>");
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
            sb.append("<td>" + summary.computeOverallCorrectnessScoreRatio() + "</td>");
            sb.append("<td>" + summary.getTrustScoreSum() + "</td>");
            sb.append("<td>" + summary.getTrustScoreCount() + "</td>");
            sb.append("<td>" + summary.computeTrustScoreRatio() + "</td>");
            sb.append("<td>" + summary.computeOverallPartialTrustScoreRatio() + "</td>");
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
                        questionInput.computeTrustScore(),
                        questionInput.computePartialTrustScore());
         
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
      
      public double[] listOverallCorrectnessScoreRatios() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.computeOverallCorrectnessScoreRatio().doubleValue();
            i++;
         }
         return result;
      }
      
      public double[] listTrustScoreRatios() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.computeTrustScoreRatio().doubleValue();
            i++;
         }
         return result;
      }
      
      public double[] listOverallPartialTrustScoreRatio() {
         double[] result = new double[participantResults.size()];
         int i = 0;
         for (ParticipantResultSummary summary : participantResults) {
            result[i] = summary.computeOverallPartialTrustScoreRatio().doubleValue();
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
      private BigDecimal correctnessScoreRatioSum = BigDecimal.ZERO; // sum of (scorePerQuestion / maxScoreOfQuestion)
      private BigInteger correctnessScoreRatioCount = BigInteger.ZERO;
      private BigInteger trustScoreSum = BigInteger.ZERO;
      private BigInteger trustScoreCount = BigInteger.ZERO;
      private BigDecimal partialTrustScoreRatioSum = BigDecimal.ZERO;
      private BigInteger partialTrustScoreRatioCount = BigInteger.ZERO;
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

      public void update(Boolean correct, 
                         BigDecimal correctnessScore, 
                         Integer trustScore,
                         BigDecimal partialTrustScore) {
         if (correct != null) {
            if (correct.booleanValue()) {
               correctCount = correctCount.add(BigInteger.ONE);
            }
            this.maxCorrectCount = this.maxCorrectCount.add(BigInteger.ONE);
         }
         if (correctnessScore != null) {
            this.correctnessScoreRatioSum = this.correctnessScoreRatioSum.add(correctnessScore);
            this.correctnessScoreRatioCount = this.correctnessScoreRatioCount.add(BigInteger.ONE);
            if (partialTrustScore != null) {
               this.partialTrustScoreRatioSum = this.partialTrustScoreRatioSum.add(partialTrustScore);
               this.partialTrustScoreRatioCount = this.partialTrustScoreRatioCount.add(BigInteger.ONE);
            }
         }
         if (trustScore != null) {
            this.trustScoreSum = this.trustScoreSum.add(BigInteger.valueOf(trustScore.intValue()));
            this.trustScoreCount = this.trustScoreCount.add(BigInteger.ONE);
         }
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

      public BigInteger getTrustScoreSum() {
         return trustScoreSum;
      }

      public BigDecimal getTimeRatio() {
         return timeRatio;
      }

      public BigInteger getTrustScoreCount() {
         return trustScoreCount;
      }

      public BigDecimal computeOverallCorrectnessScoreRatio() {
         return correctnessScoreRatioSum.divide(new BigDecimal(correctnessScoreRatioCount), 2, RoundingMode.HALF_EVEN);
      }

      public BigDecimal computeCorrectRatio() {
         return new BigDecimal(correctCount).divide(new BigDecimal(maxCorrectCount), 2, RoundingMode.HALF_EVEN);
      }

      public BigDecimal computeTrustScoreRatio() {
         return new BigDecimal(trustScoreSum).divide(new BigDecimal(trustScoreCount), 2, RoundingMode.HALF_EVEN);
      }

      public BigDecimal computeOverallPartialTrustScoreRatio() {
         return partialTrustScoreRatioSum.divide(new BigDecimal(partialTrustScoreRatioCount), 2, RoundingMode.HALF_EVEN);
      }
   }
}
