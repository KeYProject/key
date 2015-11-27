package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.definition.TabQuestion;
import org.key_project.sed.key.evaluation.model.definition.TabbedQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Exports the tool specific helpfulness questions as LaTeX file.
 * @author Martin Hentschel
 */
public class ReviewingCodeHelpfulnessExport implements IHTMLSectionAppender {
   /**
    * Indicates if filter specific files should be generated or not.
    */
   public static final boolean CREATE_FILTER_SPECIFIC_FILES = false;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      // Get questions
      Tool sed = evaluation.getTool(ReviewingCodeEvaluation.SED_TOOL_NAME);
      Tool noTool = evaluation.getTool(ReviewingCodeEvaluation.NO_TOOL_NAME);
      AbstractForm evaluationForm = evaluation.getForm(ReviewingCodeEvaluation.EVALUATION_FORM_NAME);
      QuestionPage example1page = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME);
      QuestionPage example2page = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME);
      QuestionPage example3page = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME);
      QuestionPage example4page = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME);
      QuestionPage example5page = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME);
      QuestionPage example6page = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME);
      TabbedQuestion example1Tabs = (TabbedQuestion) example1page.getQuestion(ReviewingCodeEvaluation.EXAMPLE_1_METHODS_QUESTION);
      TabQuestion example1oa = (TabQuestion) example1Tabs.getChildQuestion(ReviewingCodeEvaluation.OBSERVABLE_ARRAY_TAB_NAME);
      TabQuestion example1set = (TabQuestion) example1Tabs.getChildQuestion(ReviewingCodeEvaluation.SET_TAB_NAME);
      TabQuestion example1setAL = (TabQuestion) example1Tabs.getChildQuestion(ReviewingCodeEvaluation.SET_AL_TAB_NAME);
      TabbedQuestion example6Tabs = (TabbedQuestion) example6page.getQuestion(ReviewingCodeEvaluation.EXAMPLE_6_METHODS_QUESTION);
      TabQuestion example6Si = (TabQuestion) example6Tabs.getChildQuestion(ReviewingCodeEvaluation.STACK_INT_TAB_NAME);
      TabQuestion example6SS = (TabQuestion) example6Tabs.getChildQuestion(ReviewingCodeEvaluation.STACK_STACK_TAB_NAME);
      TabQuestion example6push = (TabQuestion) example6Tabs.getChildQuestion(ReviewingCodeEvaluation.PUSH_TAB_NAME);
      TabQuestion example6pop = (TabQuestion) example6Tabs.getChildQuestion(ReviewingCodeEvaluation.POP_TAB_NAME);
      AbstractChoicesQuestion exmaple1oaSed = (AbstractChoicesQuestion) example1oa.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple1oaExecuted = (AbstractChoicesQuestion) example1oa.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple1setSed = (AbstractChoicesQuestion) example1set.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple1setExecuted = (AbstractChoicesQuestion) example1set.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple1setALSed = (AbstractChoicesQuestion) example1setAL.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple1setALExecuted = (AbstractChoicesQuestion) example1setAL.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple2Sed = (AbstractChoicesQuestion) example2page.getQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple2Executed = (AbstractChoicesQuestion) example2page.getQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple3Sed = (AbstractChoicesQuestion) example3page.getQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple3Executed = (AbstractChoicesQuestion) example3page.getQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple4Sed = (AbstractChoicesQuestion) example4page.getQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple4Executed = (AbstractChoicesQuestion) example4page.getQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple5Sed = (AbstractChoicesQuestion) example5page.getQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple5Executed = (AbstractChoicesQuestion) example5page.getQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple6SiSed = (AbstractChoicesQuestion) example6Si.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple6SiExecuted = (AbstractChoicesQuestion) example6Si.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple6SSSed = (AbstractChoicesQuestion) example6SS.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple6SSExecuted = (AbstractChoicesQuestion) example6SS.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple6pushSed = (AbstractChoicesQuestion) example6push.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple6pushExecuted = (AbstractChoicesQuestion) example6push.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      AbstractChoicesQuestion exmaple6popSed = (AbstractChoicesQuestion) example6pop.getChildQuestion(ReviewingCodeEvaluation.SET_CONSIDERED_QUESTION);
      AbstractChoicesQuestion exmaple6popExecuted = (AbstractChoicesQuestion) example6pop.getChildQuestion(ReviewingCodeEvaluation.CODE_EXECUTED_QUESTION);
      // Compute statistics
      Map<IStatisticsFilter, HelpfulnessToolStatistic> sedStatistics = new HashMap<IStatisticsFilter, HelpfulnessToolStatistic>();
      Map<IStatisticsFilter, HelpfulnessToolStatistic> noToolStatistics = new HashMap<IStatisticsFilter, HelpfulnessToolStatistic>();
      for (IStatisticsFilter filter : statistics.getFilters()) {
         sedStatistics.put(filter, new HelpfulnessToolStatistic());
         noToolStatistics.put(filter, new HelpfulnessToolStatistic());
      }
      for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
         if (!entry.getValue().hasMultipleValues()) {
            for (IStatisticsFilter filter : statistics.getFilters()) {
               if (filter.accept(entry.getValue())) {
                  List<AbstractFormInput<?>> formInputs = entry.getValue().getFormInputs(evaluationForm);
                  if (formInputs != null && formInputs.size() == 1) { // Consider only completed evaluations.
                     updateStatistics(entry, sed, noTool, example1page, exmaple1oaSed, exmaple1oaExecuted, sedStatistics.get(filter).example1oa, noToolStatistics.get(filter).example1oa);
                     updateStatistics(entry, sed, noTool, example1page, exmaple1setSed, exmaple1setExecuted, sedStatistics.get(filter).example1set, noToolStatistics.get(filter).example1set);
                     updateStatistics(entry, sed, noTool, example1page, exmaple1setALSed, exmaple1setALExecuted, sedStatistics.get(filter).example1setAL, noToolStatistics.get(filter).example1setAL);
                     updateStatistics(entry, sed, noTool, example2page, exmaple2Sed, exmaple2Executed, sedStatistics.get(filter).example2, noToolStatistics.get(filter).example2);
                     updateStatistics(entry, sed, noTool, example3page, exmaple3Sed, exmaple3Executed, sedStatistics.get(filter).example3, noToolStatistics.get(filter).example3);
                     updateStatistics(entry, sed, noTool, example4page, exmaple4Sed, exmaple4Executed, sedStatistics.get(filter).example4, noToolStatistics.get(filter).example4);
                     updateStatistics(entry, sed, noTool, example5page, exmaple5Sed, exmaple5Executed, sedStatistics.get(filter).example5, noToolStatistics.get(filter).example5);
                     updateStatistics(entry, sed, noTool, example6page, exmaple6SiSed, exmaple6SiExecuted, sedStatistics.get(filter).example6Si, noToolStatistics.get(filter).example6Si);
                     updateStatistics(entry, sed, noTool, example6page, exmaple6SSSed, exmaple6SSExecuted, sedStatistics.get(filter).example6SS, noToolStatistics.get(filter).example6SS);
                     updateStatistics(entry, sed, noTool, example6page, exmaple6pushSed, exmaple6pushExecuted, sedStatistics.get(filter).example6push, noToolStatistics.get(filter).example6push);
                     updateStatistics(entry, sed, noTool, example6page, exmaple6popSed, exmaple6popExecuted, sedStatistics.get(filter).example6pop, noToolStatistics.get(filter).example6pop);
                  }
               }
            }
         }
      }
      // Create filter specific latex files
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
      if (CREATE_FILTER_SPECIFIC_FILES) {
         for (IStatisticsFilter filter : statistics.getFilters()) {
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_OA_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example1oa, noToolStatistics.get(filter).example1oa).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_SET_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example1set, noToolStatistics.get(filter).example1set).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_SET_AL_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example1setAL, noToolStatistics.get(filter).example1setAL).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example2, noToolStatistics.get(filter).example2).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example3, noToolStatistics.get(filter).example3).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example4, noToolStatistics.get(filter).example4).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example5, noToolStatistics.get(filter).example5).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_Si_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example6Si, noToolStatistics.get(filter).example6Si).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_SS_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example6SS, noToolStatistics.get(filter).example6SS).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_push_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example6push, noToolStatistics.get(filter).example6push).getBytes(IOUtil.DEFAULT_CHARSET)));
            additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_pop_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", 
                                createLatex(sedStatistics.get(filter).example6pop, noToolStatistics.get(filter).example6pop).getBytes(IOUtil.DEFAULT_CHARSET)));
         }
      }
      // Create filter combined latex files
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_OA.tex", 
                          createLatex(statistics.getFilters(), listExample1oa(sedStatistics), listExample1oa(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_set.tex", 
                          createLatex(statistics.getFilters(), listExample1set(sedStatistics), listExample1set(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_setAL.tex", 
                         createLatex(statistics.getFilters(), listExample1setAL(sedStatistics), listExample1setAL(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME + ".tex", 
                          createLatex(statistics.getFilters(), listExample2(sedStatistics), listExample2(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME + ".tex", 
                          createLatex(statistics.getFilters(), listExample3(sedStatistics), listExample3(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME + ".tex", 
                          createLatex(statistics.getFilters(), listExample4(sedStatistics), listExample4(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME + ".tex", 
                          createLatex(statistics.getFilters(), listExample5(sedStatistics), listExample5(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_Si.tex", 
                          createLatex(statistics.getFilters(), listExample6Si(sedStatistics), listExample6Si(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_SS.tex", 
                          createLatex(statistics.getFilters(), listExample6SS(sedStatistics), listExample6SS(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_push.tex", 
                          createLatex(statistics.getFilters(), listExample6push(sedStatistics), listExample6push(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_Helpfulness_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_pop.tex", 
                          createLatex(statistics.getFilters(), listExample6pop(sedStatistics), listExample6pop(noToolStatistics)).getBytes(IOUtil.DEFAULT_CHARSET)));
      // Create code files
      for (IStatisticsFilter filter : statistics.getFilters()) {
         addWrittenCodeFile(noToolStatistics.get(filter).example1oa, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_OA", 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_OA_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example1set, 
                           additionalFiles, 
                           "rc" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_set", 
                           "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_set_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example1setAL, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_setAL", 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_1_PAGE_NAME + "_setAL_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example2, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME, 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_2_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example3, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME, 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_3_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example4, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME, 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_4_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example5, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME, 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_5_PAGE_NAME + "_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example6Si, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_Si", 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_Si_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example6SS, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_SS", 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_SS_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example6push, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_push", 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_push_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
         addWrittenCodeFile(noToolStatistics.get(filter).example6pop, 
                            additionalFiles, 
                            "rc" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_pop", 
                            "_WrittenCode_" + ReviewingCodeEvaluation.EXAMPLE_6_PAGE_NAME + "_pop_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex");
      }
      return additionalFiles;
   }
   
   protected void addWrittenCodeFile(HelpfulnessStatistic statistic, List<AdditionalFile> additionalFiles, String idPrefix, String fileName) {
      if (!statistic.code.isEmpty()) {
         additionalFiles.add(new AdditionalFile(fileName, 
                                                createValueLatex(statistic.code, idPrefix).getBytes(IOUtil.DEFAULT_CHARSET)));
         
      }
   }
   
   protected String createValueLatex(List<String> values, String idPrefix) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\newcounter{" + idPrefix + "FeedbackRowcount}" + StringUtil.NEW_LINE);
      latex.append("\\setcounter{" + idPrefix + "FeedbackRowcount}{0}" + StringUtil.NEW_LINE);
      latex.append("\\newcommand{\\" + idPrefix + "FeedbackRowcountautorefname}{ID}" + StringUtil.NEW_LINE);
      latex.append("\\begin{tabularx}{1.0\\textwidth}{lX}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("ID & Feedback\\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      boolean afterFirst = false;
      int i = 1;
      for (String value : values) {
         if (afterFirst) {
            latex.append("\\midrule" + StringUtil.NEW_LINE);
         }
         else {
            afterFirst = true;
         }
         latex.append(i + "\\refstepcounter{" + idPrefix + "FeedbackRowcount} & ``" + value + "''\\\\" + StringUtil.NEW_LINE);
         i++;
      }
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabularx}" + StringUtil.NEW_LINE);
      return latex.toString();
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample1oa(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example1oa);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample1set(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example1set);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample1setAL(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example1setAL);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample2(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example2);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample3(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example3);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample4(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example4);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample5(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example5);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample6Si(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example6Si);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample6SS(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example6SS);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample6push(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example6push);
      }
      return result;
   }
   
   private Map<IStatisticsFilter, HelpfulnessStatistic> listExample6pop(Map<IStatisticsFilter, HelpfulnessToolStatistic> toolStatistics) {
      Map<IStatisticsFilter, HelpfulnessStatistic> result = new HashMap<IStatisticsFilter, HelpfulnessStatistic>();
      for (Entry<IStatisticsFilter, HelpfulnessToolStatistic> entry : toolStatistics.entrySet()) {
         result.put(entry.getKey(), entry.getValue().example6pop);
      }
      return result;
   }
   
   protected String createLatex(IStatisticsFilter[] filters, Map<IStatisticsFilter, HelpfulnessStatistic> sedMap, Map<IStatisticsFilter, HelpfulnessStatistic> noToolMap) {
      StringBuffer latex = new StringBuffer();
      // Header
      latex.append("\\begin{tabular}{l");
      for (int i = 0; i < filters.length; i++) {
         latex.append("rr");
      }
      latex.append("}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : filters) {
         BigInteger noMax = noToolMap.get(filter).computeMax();
         BigInteger sedMax = sedMap.get(filter).computeMax();
         latex.append(" & \\multicolumn{2}{c}{" + filter.getLatexName() + "~(" + noMax.add(sedMax) + ")}");
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : filters) {
         BigInteger noMax = noToolMap.get(filter).computeMax();
         BigInteger sedMax = sedMap.get(filter).computeMax();
         latex.append(" & \\rotatebox{90}{DCR~(" + noMax + ")}");
         latex.append(" & \\rotatebox{90}{\\SED~(" + sedMax + ")}");
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      // Very
      latex.append("Yes, Very helpful");
      for (IStatisticsFilter filter : filters) {
         BigDecimal noToolPercentage = noToolMap.get(filter).computeVeryPercentage(0);
         latex.append(" & " + (noToolPercentage != null ? noToolPercentage + "~\\%" : ""));
         BigDecimal sedPercentage = sedMap.get(filter).computeVeryPercentage(0);
         latex.append(" & " + (sedPercentage != null ? sedPercentage + "~\\%" : ""));
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      // Helpful
      latex.append("Yes, Helpful");
      for (IStatisticsFilter filter : filters) {
         BigDecimal noToolPercentage = noToolMap.get(filter).computeHelpfulPercentage(0);
         latex.append(" & " + (noToolPercentage != null ? noToolPercentage + "~\\%" : ""));
         BigDecimal sedPercentage = sedMap.get(filter).computeHelpfulPercentage(0);
         latex.append(" & " + (sedPercentage != null ? sedPercentage + "~\\%" : ""));
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      // Little
      latex.append("Yes, Little helpful");
      for (IStatisticsFilter filter : filters) {
         BigDecimal noToolPercentage = noToolMap.get(filter).computeLittlePercentage(0);
         latex.append(" & " + (noToolPercentage != null ? noToolPercentage + "~\\%" : ""));
         BigDecimal sedPercentage = sedMap.get(filter).computeLittlePercentage(0);
         latex.append(" & " + (sedPercentage != null ? sedPercentage + "~\\%" : ""));
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      // Not Helpful
      latex.append("No, Not helpful");
      for (IStatisticsFilter filter : filters) {
         BigDecimal noToolPercentage = noToolMap.get(filter).computeNotHeplfulPercentage(0);
         latex.append(" & " + (noToolPercentage != null ? noToolPercentage + "~\\%" : ""));
         BigDecimal sedPercentage = sedMap.get(filter).computeNotHeplfulPercentage(0);
         latex.append(" & " + (sedPercentage != null ? sedPercentage + "~\\%" : ""));
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      // Not considered
      latex.append("Not considered");
      for (IStatisticsFilter filter : filters) {
         BigDecimal noToolPercentage = noToolMap.get(filter).computeNotConsideredPercentage(0);
         latex.append(" & " + (noToolPercentage != null ? noToolPercentage + "~\\%" : ""));
         BigDecimal sedPercentage = sedMap.get(filter).computeNotConsideredPercentage(0);
         latex.append(" & " + (sedPercentage != null ? sedPercentage + "~\\%" : ""));
      }
      latex.append(" \\\\" + StringUtil.NEW_LINE);
      // Footer
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
      return latex.toString();
   }
   
   protected String createLatex(HelpfulnessStatistic sed, HelpfulnessStatistic noTool) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabular}{lrr}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("& \\SED (\\%) & DCR (\\%) \\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      latex.append("Yes, Very helpful & " + sed.computeVeryPercentage(0) + " & " + noTool.computeVeryPercentage(0) + " \\\\" + StringUtil.NEW_LINE);
      latex.append("Yes, Helpful & " + sed.computeHelpfulPercentage(0) + " & " + noTool.computeHelpfulPercentage(0) + " \\\\" + StringUtil.NEW_LINE);
      latex.append("Yes, Little helpful & " + sed.computeLittlePercentage(0) + " & " + noTool.computeLittlePercentage(0) + " \\\\" + StringUtil.NEW_LINE);
      latex.append("No, Not helpful & " + sed.computeNotHeplfulPercentage(0) + " & " + noTool.computeNotHeplfulPercentage(0) + " \\\\" + StringUtil.NEW_LINE);
      latex.append("Not considered & " + sed.computeNotConsideredPercentage(0) + " & " + noTool.computeNotConsideredPercentage(0) + " \\\\" + StringUtil.NEW_LINE);
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
      return latex.toString();
   }
   
   protected void updateStatistics(Entry<String, EvaluationAnswers> entry, 
                                   Tool sed,
                                   Tool noTool,
                                   QuestionPage page,
                                   AbstractChoicesQuestion sedQuestion,
                                   AbstractChoicesQuestion noToolQuestion,
                                   HelpfulnessStatistic sedStatistics,
                                   HelpfulnessStatistic noToolStatistics) {
      List<Tool> tools = entry.getValue().getTools(page);
      if (tools != null && tools.size() == 1) {
         Tool tool = tools.get(0);
         if (sed.equals(tool)) {
            List<QuestionInput> qis = entry.getValue().getQuestionInputs(sedQuestion);
            if (qis != null) {
               QuestionInput qi = qis.get(0);
               if (ReviewingCodeEvaluation.SET_CONSIDERED_VERY_HELPFUL_VALUE.equals(qi.getValue())) {
                  sedStatistics.increaseVery();
               }
               else if (ReviewingCodeEvaluation.SET_CONSIDERED_HELPFUL_VALUE.equals(qi.getValue())) {
                  sedStatistics.increaseHelpful();
               }
               else if (ReviewingCodeEvaluation.SET_CONSIDERED_LITTLE_HELPFUL_VALUE.equals(qi.getValue())) {
                  sedStatistics.increaseLittle();
               }
               else if (ReviewingCodeEvaluation.SET_CONSIDERED_NOT_HELPFUL_VALUE.equals(qi.getValue())) {
                  sedStatistics.increaseNotHelpful();
               }
               else if (ReviewingCodeEvaluation.SET_CONSIDERED_NOT_CONSIDERED_VALUE.equals(qi.getValue())) {
                  sedStatistics.increaseNotConsidered();
               }
               else if (qi.getValue() == null) {
                  // Nothing to do, participant cancelled evaluation.
               }
               else { 
                  throw new IllegalStateException("Reviewing Code Evaluation has changed, value '" + qi.getValue() + "' of '" + entry.getKey() + "' is unknown.");
               }
            }
            else {
               throw new IllegalStateException("Single answer of " + entry.getKey() + " is not available.");
            }
         }
         else if (noTool.equals(tool)) {
            List<QuestionInput> qis = entry.getValue().getQuestionInputs(noToolQuestion);
            if (qis != null) {
               QuestionInput qi = qis.get(0);
               if (ReviewingCodeEvaluation.EXECUTED_YES_VALUE.equals(qi.getValue())) {
                  QuestionInput[] choiceInputs = qi.getChoiceInputs(noToolQuestion.getChoice(ReviewingCodeEvaluation.EXECUTED_YES_VALUE));
                  QuestionInput helpfulInput = choiceInputs[0];
                  if (ReviewingCodeEvaluation.EXECUTED_HELPFUL_QUESTION.equals(helpfulInput.getQuestion().getName())) {
                     if (ReviewingCodeEvaluation.EXECUTED_VERY_HELPFUL_VALUE.equals(helpfulInput.getValue())) {
                        noToolStatistics.increaseVery();
                     }
                     else if (ReviewingCodeEvaluation.EXECUTED_HELPFUL_VALUE.equals(helpfulInput.getValue())) {
                        noToolStatistics.increaseHelpful();
                     }
                     else if (ReviewingCodeEvaluation.EXECUTED_LITTLE_HELPFUL_VALUE.equals(helpfulInput.getValue())) {
                        noToolStatistics.increaseLittle();
                     }
                     else if (ReviewingCodeEvaluation.EXECUTED_NOT_HELPFUL_VALUE.equals(helpfulInput.getValue())) {
                        noToolStatistics.increaseNotHelpful();
                     }
                     else if (qi.getValue() == null) {
                        // Nothing to do, participant cancelled evaluation.
                     }
                     else { 
                        throw new IllegalStateException("Reviewing Code Evaluation has changed.");
                     }
                  }
                  else {
                     throw new IllegalStateException("Reviewing Code Evaluation has changed, value '" + helpfulInput.getValue() + "' of '" + entry.getKey() + "' is unknown.");
                  }
                  QuestionInput codeInput = choiceInputs[1];
                  if (ReviewingCodeEvaluation.WRITTEN_CODE_QUESTION.equals(codeInput.getQuestion().getName())) {
                     if (!StringUtil.isTrimmedEmpty(codeInput.getValue())) {
                        noToolStatistics.code.add(codeInput.getValue());
                     }
                  }
                  else {
                     throw new IllegalStateException("Reviewing Code Evaluation has changed, value '" + helpfulInput.getValue() + "' of '" + entry.getKey() + "' is unknown.");
                  }
               }
               else if (ReviewingCodeEvaluation.EXECUTED_NO_VALUE.equals(qi.getValue())) {
                  noToolStatistics.increaseNotConsidered();
               }
               else if (qi.getValue() == null) {
                  // Nothing to do, participant cancelled evaluation.
               }
               else {
                  throw new IllegalStateException("Reviewing Code Evaluation has changed, value '" + qi.getValue() + "' of '" + entry.getKey() + "' is unknown.");
               }
            }
            else {
               throw new IllegalStateException("Single answer of " + entry.getKey() + " is not available.");
            }
         }
         else {
            throw new IllegalStateException("Reviewing Code Evaluation has changed.");
         }
      }
   }
   
   private static class HelpfulnessToolStatistic {
      private HelpfulnessStatistic example1oa = new HelpfulnessStatistic();
      private HelpfulnessStatistic example1set = new HelpfulnessStatistic();
      private HelpfulnessStatistic example1setAL = new HelpfulnessStatistic();
      private HelpfulnessStatistic example2 = new HelpfulnessStatistic();
      private HelpfulnessStatistic example3 = new HelpfulnessStatistic();
      private HelpfulnessStatistic example4 = new HelpfulnessStatistic();
      private HelpfulnessStatistic example5 = new HelpfulnessStatistic();
      private HelpfulnessStatistic example6Si = new HelpfulnessStatistic();
      private HelpfulnessStatistic example6SS = new HelpfulnessStatistic();
      private HelpfulnessStatistic example6push = new HelpfulnessStatistic();
      private HelpfulnessStatistic example6pop = new HelpfulnessStatistic();
   }
   
   private static class HelpfulnessStatistic {
      private BigInteger very = BigInteger.ZERO;
      private BigInteger helpful = BigInteger.ZERO;
      private BigInteger little = BigInteger.ZERO;
      private BigInteger notHelpful = BigInteger.ZERO;
      private BigInteger notConsidered = BigInteger.ZERO;
      private List<String> code = new LinkedList<String>();
      
      public void increaseVery() {
         very = very.add(BigInteger.ONE);
      }
      
      public void increaseHelpful() {
         helpful = helpful.add(BigInteger.ONE);
      }
      
      public void increaseLittle() {
         little = little.add(BigInteger.ONE);
      }
      
      public void increaseNotHelpful() {
         notHelpful = notHelpful.add(BigInteger.ONE);
      }
      
      public void increaseNotConsidered() {
         notConsidered = notConsidered.add(BigInteger.ONE);
      }
      
      public BigInteger computeMax() {
         return very.add(helpful).add(little).add(notHelpful).add(notConsidered);
      }
      
      public BigDecimal computeVeryPercentage(int decimalDigits) {
         return computePercentage(very, decimalDigits);
      }
      
      public BigDecimal computeHelpfulPercentage(int decimalDigits) {
         return computePercentage(helpful, decimalDigits);
      }
      
      public BigDecimal computeLittlePercentage(int decimalDigits) {
         return computePercentage(little, decimalDigits);
      }
      
      public BigDecimal computeNotHeplfulPercentage(int decimalDigits) {
         return computePercentage(notHelpful, decimalDigits);
      }
      
      public BigDecimal computeNotConsideredPercentage(int decimalDigits) {
         return computePercentage(notConsidered, decimalDigits);
      }
      
      private BigDecimal computePercentage(BigInteger value, int decimalDigits) {
         BigInteger mul100 = value.multiply(BigInteger.valueOf(100));
         BigInteger maxCount = computeMax();
         if (!maxCount.equals(BigInteger.ZERO)) {
            return new BigDecimal(mul100).divide(new BigDecimal(maxCount), decimalDigits, RoundingMode.HALF_EVEN);
         }
         else {
            return null;
         }
      }
   }
}
