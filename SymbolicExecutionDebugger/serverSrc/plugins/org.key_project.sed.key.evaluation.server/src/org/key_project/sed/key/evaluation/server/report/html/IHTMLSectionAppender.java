package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.HTMLReportEngine;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;

/**
 * Instances of this class are used to append a section on an HTML report
 * created by an {@link HTMLReportEngine}.
 * @author Martin Hentschel
 */
public interface IHTMLSectionAppender {
   /**
    * Appends the computed section to the HTML report.
    * @param The current storage location.
    * @param evaluation The analyzed {@link AbstractEvaluation}.
    * @param The computed {@link EvaluationResult}.
    * @param statistics The computed {@link Statistics}s.
    * @param sb The {@link StringBuffer} to append to.
    */   
   public void appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb);
}
