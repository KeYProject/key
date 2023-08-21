/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import java.io.File;
import java.util.Collections;
import java.util.concurrent.ExecutionException;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.junit.jupiter.api.Test;

/**
 * @author Alexander Weigl
 * @version 1 (29.01.23)
 */
class JavaCompilerCheckFacadeTest {
    @Test
    void compile1() throws ExecutionException, InterruptedException {
        File src = new File("examples/firstTouch/06-BinarySearch/src/").getAbsoluteFile();
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
            JavaCompilerCheckFacade.check(emptyListener, null, Collections.emptyList(), src);
        promise.get();
    }

}
