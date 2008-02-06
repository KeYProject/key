// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;

import recoder.CrossReferenceServiceConfiguration;
import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.convenience.TreeWalker;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.reference.TypeReference;
import recoder.list.CompilationUnitList;
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

        CompilationUnitList cus = sfr.getCompilationUnits();
        for (int i = 0; i < cus.size(); i++) {
            TreeWalker walker = new TreeWalker(cus.getProgramElement(i));
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
        File[] files = dir.listFiles();
        for (int i = 0; i < files.length; i++) {
            if (files[i].isDirectory())
                handleDir(files[i]);
            else
                readFile(files[i]);
        }
    }

    private static void readFile(File file) throws ParserException, IOException {
        if (!file.getName().toLowerCase().endsWith(".java"))
            return;

        System.err.println("Parsing: " + file);

        ProgramFactory factory = sc.getProgramFactory();
        CompilationUnit cu = factory.parseCompilationUnit(new FileReader(file));
        cu.makeAllParentRolesValid();
        sc.getChangeHistory().attached(cu);
    }

}

class RefSolverServiceConfiguration extends CrossReferenceServiceConfiguration {
    protected ProgramFactory makeProgramFactory() {
        return ProofJavaProgramFactory.getInstance();
    }
}