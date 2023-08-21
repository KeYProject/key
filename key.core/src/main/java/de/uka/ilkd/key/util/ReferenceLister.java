/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.CrossReferenceServiceConfiguration;
import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.reference.TypeReference;
import recoder.service.SourceInfo;

/**
 * Find out for a collection of Java files which referenced types are not defined within the source
 * directory. Stubs using empty method or constructor bodies are allowed.
 *
 * @author MU
 *
 */
public class ReferenceLister {
    private static final Logger LOGGER = LoggerFactory.getLogger(ReferenceLister.class);

    private static DefaultServiceConfiguration sc;

    public static void main(String[] args) throws ParserException, IOException {
        LOGGER.info("Use this program to print unresolved type references.");
        LOGGER.info("Call with one argument: The directory to read java files from (recursively).");

        sc = new RefSolverServiceConfiguration();

        File dir = new File(args[0]);

        handleDir(dir);

        SourceFileRepository sfr = sc.getSourceFileRepository();
        SourceInfo si = sc.getSourceInfo();

        List<CompilationUnit> cus = sfr.getCompilationUnits();
        for (CompilationUnit cu : cus) {
            TreeWalker walker = new TreeWalker(cu);
            while (walker.next()) {
                ProgramElement pe = walker.getProgramElement();
                if (pe instanceof TypeReference) {
                    TypeReference typeRef = (TypeReference) pe;
                    if (si.getType(typeRef) == null && !typeRef.getName().equals("void")) {
                        LOGGER.info("Unresolvable type: {}", typeRef.toSource());
                    }
                }
            }
        }
    }

    private static void handleDir(File dir) throws ParserException, IOException {
        assert dir.isDirectory();
        File[] files = dir.listFiles();
        for (File file : Objects.requireNonNull(files)) {
            if (file.isDirectory()) {
                handleDir(file);
            } else {
                readFile(file);
            }
        }
    }

    private static void readFile(File file) throws ParserException, IOException {
        if (!file.getName().toLowerCase().endsWith(".java")) {
            return;
        }

        LOGGER.warn("Parsing: {}", file);

        ProgramFactory factory = sc.getProgramFactory();
        FileReader fileReader = new FileReader(file, StandardCharsets.UTF_8);
        final CompilationUnit cu;
        try {
            cu = factory.parseCompilationUnit(fileReader);
        } finally {
            fileReader.close();
        }
        cu.makeAllParentRolesValid();
        sc.getChangeHistory().attached(cu);
    }

}


class RefSolverServiceConfiguration extends CrossReferenceServiceConfiguration {
    @Override
    protected ProgramFactory makeProgramFactory() {
        return ProofJavaProgramFactory.getInstance();
    }
}
