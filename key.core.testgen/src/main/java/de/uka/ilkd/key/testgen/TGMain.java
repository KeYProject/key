/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLog;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.util.Objects;

public class TGMain {
    private final static Logger LOGGER = LoggerFactory.getLogger("main");

    public static void main(String[] args) throws ProblemLoaderException, InterruptedException {
        if (SolverTypes.Z3_CE_SOLVER.checkForSupport()) {
            LOGGER.error("Z3 not found! Bye.");
            System.exit(1);
            return;
        } else {
            LOGGER.info("Z3 found; Version {}", SolverTypes.Z3_CE_SOLVER.getInstalledVersion());
        }


        var settings = new TestGenerationSettings();
        String fileName = null;
        for (int i = 0; i < args.length; i++) {
            var a = args[i];
            if (a.startsWith("--")) {
                switch (a) {
                    case "--output" -> settings.setOutputPath(args[++i]);
                    case "--rfl" -> settings.setRFL(true);
                    case "--format" -> settings.setFormat(Format.valueOf(args[++i]));
                }
            } else {
                fileName = a;
            }
        }

        var env = KeYEnvironment.load(new File(Objects.requireNonNull(fileName)));
        TestGenerationLog log = new SysoutTestGenerationLog();
        Proof proof = env.getLoadedProof();
        TestgenFacade.generateTestcases(env, proof, settings, log);
    }

    private static class SysoutTestGenerationLog implements TestGenerationLog {
        @Override
        public void writeln(String string) {
            LOGGER.info(string);
        }

        @Override
        public void writeException(Throwable t) {
            LOGGER.error("Error occurred!", t);
        }

        @Override
        public void testGenerationCompleted() {
        }
    }
}
