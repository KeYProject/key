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

package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.util.List;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.PositionedString;


/** 
 * Represents an entity read to produce an environment to read a proof
 * obligation. Environment means the initial configuration of a prover
 * containing namespaces and Java model.
 */
public interface EnvInput {

    /**
     * Returns the name of this input.
     */
    String name();

    /**
     * Returns the total numbers of chars that can be read in this input.
     */
    int getNumberOfChars();

    /**
     * Sets the initial configuration the read environment input should be
     * added to. Must be called before calling any of the read* methods.
     */
    void setInitConfig(InitConfig initConfig);

    /**
     * Reads the include section and returns an Includes object.
     */
    Includes readIncludes() throws ProofInputException;

    /**
     * Reads the Java path.
     */
    String readJavaPath() throws ProofInputException;

    /**
     * Returns the file path to specific requested Java file.
     *
     * @see #isIgnoreOtherJavaFiles()
     */
    default @Nullable String getJavaFile() throws ProofInputException {
        return null;
    }


    /**
     * gets the classpath elements to be considered here.
     */
    @Nonnull List<File> readClassPath() throws ProofInputException;

    /**
     * gets the boot classpath element, null if none set.
     * @throws  
     */
    File readBootClassPath() throws IOException;
    
    /**
     * Reads the input using the given modification strategy, i.e.,
     * parts of the input do not modify the initial configuration while
     * others do.
     * @return The found warnings or an empty {@link ImmutableSet} if no warnings occurred.
     */
    ImmutableSet<PositionedString> read() throws ProofInputException;
    
    /**
     * Returns the {@link Profile} to use.
     * @return The {@link Profile} to use.
     */
    Profile getProfile();

    /**
     * Returns the initial {@link File} which is loaded if available.
     * @return The initial {@link File} which is loaded or {@code null} otherwise.
     */
    File getInitialFile();

    /**
     * This flag determines whether the given path to the Java source should be considered as a classpath,
     * or just the Java file without other files should be loaded.
     * <p>
     * Default is false.
     * <p>
     *     If true, the requested Java file has to given via {@link #getJavaFile()}.
     * </p>
     * @see de.uka.ilkd.key.proof.init.ProblemInitializer#readJava(EnvInput, InitConfig)
     */
    default boolean isIgnoreOtherJavaFiles() {return false;}
}
