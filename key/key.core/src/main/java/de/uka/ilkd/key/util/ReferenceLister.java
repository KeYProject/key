// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.List;

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
import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;

/**
 * Find out for a collection of Java files which referenced types are not defined
 * within the source directory. Stubs using empty method or constructor bodies
 * are allowed.
 * 
 * @author MU
 * 
 */
public class ReferenceLister {

    private static DefaultServiceConfiguration sc;

    public static void main(String[] args) throws ParserException, IOException {

        System.err
                .println("Use this program to print unresolved type references.");
        System.err
                .println("Call with one argument: The directory to read java files from (recursively).");

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
                    if (si.getType(typeRef) == null
                            && !typeRef.getName().equals("void"))
                        System.out.println("Unresolvable type: "
                                + typeRef.toSource());
                }
            }
        }
    }

    private static void handleDir(File dir) throws ParserException, IOException {
        assert dir.isDirectory();
        File[] files = dir.listFiles();
        for (File file : files) {
            if (file.isDirectory())
                handleDir(file);
            else
                readFile(file);
        }
    }

    private static void readFile(File file) throws ParserException, IOException {
        if (!file.getName().toLowerCase().endsWith(".java"))
            return;

        System.err.println("Parsing: " + file);

        ProgramFactory factory = sc.getProgramFactory();
        FileReader fileReader = new FileReader(file);
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
    protected ProgramFactory makeProgramFactory() {
        return ProofJavaProgramFactory.getInstance();
    }
}