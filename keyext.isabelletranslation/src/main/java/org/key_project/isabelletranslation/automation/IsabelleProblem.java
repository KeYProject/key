/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class represents an Isabelle problem. It contains the goal corresponding to the problem, as
 * well as the content of the preamble and translation theory.
 *
 * @author Nils Buchholz
 */
public class IsabelleProblem {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleProblem.class);

    /**
     * The goal associated with this problem
     */
    private final Goal goal;

    /**
     * Content of the preamble theory
     */
    private final String preamble;

    /**
     * Content of the translation theory
     */
    private final String translation;

    /**
     * Name of the problem. Contains the serialNr of the associated goal
     * Used to display the goal in the rows of Isabelle dialogs
     */
    private final String name;

    /**
     * Exception encountered during translation
     */
    private final IllegalFormulaException exception;

    /**
     * Creates a new problem for the given goal.
     *
     * @param goal the goal associated with this problem
     * @param preamble content of the preamble theory
     * @param translation content of the translation theory
     */
    public IsabelleProblem(Goal goal, String preamble, String translation) {
        this.goal = goal;
        this.preamble = preamble;
        this.translation = translation;
        this.name = "Goal " + goal.node().serialNr();
        this.exception = null;
    }

    public IsabelleProblem(Goal goal, IllegalFormulaException exception) {
        this.goal = goal;
        this.preamble = null;
        this.translation = null;
        this.name = "Goal " + goal.node().serialNr();
        this.exception = exception;
    }

    /**
     * Returns goal associated with this problem.
     *
     * @return goal associated with this problem
     */
    public Goal getGoal() {
        return goal;
    }

    /**
     * Returns content of translation theory
     *
     * @return content of translation theory
     */
    public String getTranslation() {
        return translation;
    }

    /**
     * Returns content of preamble theory
     *
     * @return content of preamble theory
     */
    public String getPreamble() {
        return preamble;
    }

    /**
     * Returns the name of this problem
     *
     * @return the name of this problem
     */
    public String getName() {
        return name;
    }

    /**
     * Writes the contents of the preamble and translation theory to the files specified in the
     * {@link IsabelleTranslationSettings}.
     * If the files and directories are not already present, they are created.
     *
     * @param settings settings to be used
     */
    public void writeTranslationFiles(IsabelleTranslationSettings settings) throws IOException {
        File translationFile = new File(settings.getTranslationPath() + "/Translation.thy");
        File translationPreambleFile =
            new File(settings.getTranslationPath() + "/TranslationPreamble.thy");
        Files.createDirectories(translationFile.toPath().getParent());
        Files.write(translationPreambleFile.toPath(), this.getPreamble().getBytes());
        Files.write(translationFile.toPath(), this.getTranslation().getBytes());
        LOGGER.info("Saved to: {} and {}", translationFile.toPath(),
            translationPreambleFile.toPath());
    }

    /**
     * Checks if a translation, preamble are present
     *
     * @return true - both translation and preamble are present, false - otherwise
     */
    public boolean hasTranslation() {
        return translation != null || preamble != null;
    }

    public IllegalFormulaException getTranslationException() {
        return exception;
    }
}
