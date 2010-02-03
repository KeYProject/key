// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import de.uka.ilkd.key.java.ConvertException;

import recoder.ProgramFactory;
import recoder.bytecode.*;
import recoder.io.DataLocation;
import recoder.java.CompilationUnit;

/**
 * This class provides an infrastructure to read in multiple class files and to
 * manufacture ClassDeclarations out of them.
 * 
 * If inner classes are present, more than one class file may be put into a
 * class declaration. This manager uses {@link ClassFileDeclarationBuilder}
 * objects to actually create source objects from classes and keeps track of the
 * changes.
 * 
 * It allows to retrieve a collection of compilation units in the end.
 * 
 * @author MU
 * 
 */
public class ClassFileDeclarationManager {

    private Map<String, CompilationUnit> compUnits = new HashMap<String, CompilationUnit>();

    private List<ClassFileDeclarationBuilder> innerClassBuilders = new ArrayList<ClassFileDeclarationBuilder>();

    private ProgramFactory programFactory;

    /**
     * create a new ClassFileDeclarationManager
     * @param programFactory Factory to be used for the creation of the type declarations.
     */
    public ClassFileDeclarationManager(ProgramFactory programFactory) {
        super();
        this.programFactory = programFactory;
    }

    /**
     * retrieve all stores compilation units.
     * 
     * This method makes sure that prior to returning all known inner classses
     * are appended as members to the corresponding enclosing classes
     * 
     * @return a collection of compilation units
     * @throws ConvertException
     *                 if an inner class cannot be connected to the enclosing
     *                 class, e.g. if this is not present
     */
    public Collection<? extends CompilationUnit> getCompilationUnits() throws ConvertException {
        attachInnerClasses();
        return compUnits.values();
    }

    /*
     * iterate the inner classes and add them to the according enclosing classes.
     */
    private void attachInnerClasses() throws ConvertException {

        for (ClassFileDeclarationBuilder innerClass : innerClassBuilders) {
            try {
                String enclName = innerClass.getEnclosingName();
                
                CompilationUnit enclCU = compUnits.get(enclName);
                if(enclCU == null)
                    throw new ConvertException("The enclosing class '" + enclName +
                            "' for class '" + innerClass.getFullClassname() + "' is not present");
                
                innerClass.attachToEnclosingCompilationUnit(enclCU);
            } catch (Exception ex) {
                throw new ConvertException("Error while attaching: " + 
                        innerClass.getFullClassname(), ex);
            }
        }
        innerClassBuilders.clear();
    }

    /**
     * add a class file which is to be transformed into a stub. Create a
     * compilation unit if the class file is no inner class. Otherwise remember
     * the builder to resolve it later.
     * 
     * @param cf
     *                Classfile to add
     * @param dataLocation
     *                location to be stored in the created stub.
     */
    public void addClassFile(ClassFile cf, DataLocation dataLocation) {
        ClassFileDeclarationBuilder builder = new ClassFileDeclarationBuilder(
                programFactory, cf);
        builder.setDataLocation(dataLocation);

        if (builder.isInnerClass()) {
            innerClassBuilders.add(builder);
        } else {
            CompilationUnit cu = builder.makeCompilationUnit();
            compUnits.put(builder.getFullClassname(), cu);
        }
    }

}
