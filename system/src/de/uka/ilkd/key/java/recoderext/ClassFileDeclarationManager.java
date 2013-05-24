// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.recoderext;

import java.io.File;
import java.io.FileWriter;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.bytecode.ByteCodeParser;
import recoder.bytecode.ClassFile;
import recoder.io.DataLocation;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;
import recoder.service.KeYCrossReferenceSourceInfo;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.FileCollection.Walker;

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
 * Only toplevel classes and their embedded classes are created. Anonymous
 * classes and classes which are declared within the code are NOT translated.
 * 
 * @see ClassFileDeclarationBuilder
 * @author MU
 * 
 */
public class ClassFileDeclarationManager {

    private List<CompilationUnit> compUnits = new ArrayList<CompilationUnit>();

    private List<ClassFileDeclarationBuilder> builderList = new ArrayList<ClassFileDeclarationBuilder>();

    private ProgramFactory programFactory;

    private Map<String, ClassFileDeclarationBuilder> classBuilders = 
        new LinkedHashMap<String, ClassFileDeclarationBuilder>();
    
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
        processBuilders();
        return compUnits;
    }

    /*
     * iterate the inner classes and add them to the according enclosing classes.,
     * 
     * The list of inner classes is sorted lexicographically so that any inner
     * classes has been added before their (even more) inner classes appear.  
     */
    private void processBuilders() throws ConvertException {
        
        Collections.sort(builderList);
        for (ClassFileDeclarationBuilder builder : builderList) {
            try {
                if(builder.isInnerClass()) {
                    builder.attachToEnclosingDeclaration();
                } else if(!builder.isAnonymousClass()){
                    compUnits.add(builder.makeCompilationUnit());   
                }
            } catch (Exception ex) {
                throw new ConvertException("Error while processing: " + 
                        builder.getFullClassname(), ex);
            }
        }
        builderList.clear();
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
        ClassFileDeclarationBuilder builder = new ClassFileDeclarationBuilder(this, cf);
        builder.setDataLocation(dataLocation);
        classBuilders.put(builder.getFullClassname(), builder);
        builderList.add(builder);
    }
    
    /**
     * get the program factory associated with this manager
     * @return the program factory, not null
     */
    public ProgramFactory getProgramFactory() {
        return programFactory;
    }


    /**
     * retrieve a specific builder from the database of builders.
     * 
     * @param className
     *                class to get a builder for.
     * @return a builder for the given className or null if no builder is stored
     */
    public ClassFileDeclarationBuilder getBuilder(String className) {
        return classBuilders.get(className);
    }


    /**
     * Test the class creation mechanism.
     * 
     * Arguments: 
     * 1. Directory that contains .class files
     * 2. Directory to write resulting .java files to
     * 
     * The test procedure is to run this program on the JDK java.* packages
     * There should be no error.
     * 
     * @throws Exception all kinds of exceptions
     */
    public static void main(String[] args) throws Exception {
        
        ClassFileDeclarationManager manager = new ClassFileDeclarationManager(JavaProgramFactory.getInstance()); 
        ByteCodeParser parser = new ByteCodeParser();
        
        FileCollection fileColl = new DirectoryFileCollection(new File(args[0]));
        Walker walker = fileColl.createWalker(".class");
        
        while(walker.step()) {
            try {
                DataLocation currentDataLocation = walker.getCurrentDataLocation();
                System.out.println("Now reading: " + currentDataLocation);
                InputStream is = walker.openCurrent();
                ClassFile cf;
                try { 
                    cf = parser.parseClassFile(is);
                } finally {
                    is.close();
                }
                manager.addClassFile(cf, currentDataLocation);
            } catch(Exception ex) {
                throw new Exception("Error while loading: " + walker.getCurrentDataLocation(), ex);
            }
        }
        
        ServiceConfiguration sc = new KeYCrossReferenceServiceConfiguration(
                new KeYRecoderExcHandler());
        KeYCrossReferenceSourceInfo sourceInfo = (KeYCrossReferenceSourceInfo)sc.getSourceInfo();
        sourceInfo.setIgnoreUnresolvedClasses(true);
        
        for (CompilationUnit cu : manager.getCompilationUnits()) {
            sc.getChangeHistory().attached(cu);
        }
        for (CompilationUnit cu : sourceInfo.getCreatedStubClasses()) {
            sc.getChangeHistory().attached(cu);
        }
        sc.getChangeHistory().updateModel();
        for (CompilationUnit cu : manager.getCompilationUnits()) {
            String name = cu.getPrimaryTypeDeclaration().getFullName();
            System.out.println("Generating " + name);
            FileWriter fw = new FileWriter(new File(args[1], name + ".jstub"));
            fw.write(cu.toSource());
            fw.close();
        }
        for (CompilationUnit cu : sourceInfo.getCreatedStubClasses()) {
            String name = cu.getPrimaryTypeDeclaration().getFullName();
            System.out.println("Generating empty stub " + name);
            FileWriter fw = new FileWriter(new File(args[1], name + ".jstub"));
            fw.write(cu.toSource());
            fw.close();
        }
    }

}
