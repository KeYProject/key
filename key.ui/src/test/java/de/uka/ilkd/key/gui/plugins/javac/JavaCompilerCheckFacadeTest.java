/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Arrays;
import java.util.Collections;
import java.util.concurrent.ExecutionException;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.gui.PositionedIssueString;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (29.01.23)
 */
class JavaCompilerCheckFacadeTest {
    @Test
    void compile1() throws ExecutionException, InterruptedException {
        Path src = Paths.get("examples/firstTouch/06-BinarySearch/src/");
        assertEquals(checkFile(src, Collections.emptyList()).size(), 0);
    }

    @Test 
    void compileUniverseCorrect() throws ExecutionException, InterruptedException { 
        Path src = Paths.get("src/test/recources/plugins/javac/Correct.java");
        assertEquals(checkFile(src, Arrays.asList("universe.UniverseChecker")).size(), 0);
    }

    @Test
    void compileUniverseIncorrect() throws ExecutionException, InterruptedException, IOException {
        Path src = Paths.get("src/test/recources/plugins/javac/Incorrect.java");
        assertEquals(checkFile(src, Collections.emptyList()).size(), 0);
        assertEquals(checkFile(src, Arrays.asList("universe.UniverseChecker")).size(), 1);
    }

    List<PositionedIssueString> checkFile(Path src, List<String> processors) throws ExecutionException, InterruptedException  {
        System.out.println(src);
        ProblemInitializer.ProblemInitializerListener emptyListener =
            new ProblemInitializer.ProblemInitializerListener() {
                @Override
                public void proofCreated(ProblemInitializer sender,
                        ProofAggregate proofAggregate) {}

                @Override
                public void progressStarted(Object sender) {}

                @Override
                public void progressStopped(Object sender) {}

                @Override
                public void reportStatus(Object sender, String status, int progress) {}

                @Override
                public void reportStatus(Object sender, String status) {}

                @Override
                public void resetStatus(Object sender) {}

                @Override
                public void reportException(Object sender, ProofOblInput input, Exception e) {}
            };
        var promise =
            JavaCompilerCheckFacade.check(emptyListener, null, Collections.emptyList(),
                src, processors);
        return promise.get();
    }
}
