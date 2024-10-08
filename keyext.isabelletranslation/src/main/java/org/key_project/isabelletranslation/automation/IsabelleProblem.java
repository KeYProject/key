package org.key_project.isabelletranslation.automation;

import de.uka.ilkd.key.proof.Goal;
import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

public class IsabelleProblem {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleProblem.class);

    private final Goal goal;
    private final String preamble;
    private final String sequentTranslation;
    private final String name;

    public IsabelleProblem(Goal goal, String preamble, String sequentTranslation) {
        this.goal = goal;
        this.preamble = preamble;
        this.sequentTranslation = sequentTranslation;
        this.name = "Goal " + goal.node().serialNr();
    }

    public Goal getGoal() {
        return goal;
    }

    public String getSequentTranslation() {
        return sequentTranslation;
    }

    public String getPreamble() {
        return preamble;
    }

    public String getName() {
        return name;
    }

    public void writeTranslationFiles(IsabelleTranslationSettings settings) {
        File translationFile = new File(settings.getTranslationPath() + "/Translation.thy");
        File translationPreambleFile = new File(settings.getTranslationPath() + "/TranslationPreamble.thy");
        try {
            Files.createDirectories(translationFile.toPath().getParent());
            Files.write(translationPreambleFile.toPath(), this.getPreamble().getBytes());
            Files.write(translationFile.toPath(), this.getSequentTranslation().getBytes());
            LOGGER.info("Saved to: {} and {}", translationFile.toPath(), translationPreambleFile.toPath());
        } catch (IOException e) {
            LOGGER.error("Failed to save translation", e);
        }
    }
}
