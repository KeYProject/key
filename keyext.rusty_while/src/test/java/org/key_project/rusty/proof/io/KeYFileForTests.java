/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.parser.KeYIO;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.init.ProofInputException;
import org.key_project.rusty.rule.Taclet;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

public class KeYFileForTests extends KeYFile {
    private Namespace<@NonNull QuantifiableVariable> variables;
    private Namespace<@NonNull SchemaVariable> schemaVariables;

    /**
     * creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     */
    public KeYFileForTests(String name, File file, Profile profile) {
        super(name, file, profile);
    }

    /**
     * reads the whole .key file and modifies the initial configuration assigned to this object
     * according to the given modification strategy. Throws an exception if no initial configuration
     * has been set yet.
     */
    @Override
    public ImmutableSet<String> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("KeYFile: InitConfig not set.");
        }
        BufferedReader cinp = null;
        try {
            cinp =
                new BufferedReader(new InputStreamReader(getNewStream()), getNumberOfChars() / 100);
            KeYIO io = new KeYIO(initConfig.getServices());
            KeYIO.Loader l = io.load(file.getCharStream());
            List<Taclet> taclets = l.loadComplete();
            initConfig.addTaclets(taclets);

            variables = new Namespace<>(); // problemParser.namespaces().variables().copy();
            schemaVariables = l.getSchemaNamespace();

            return DefaultImmutableSet.nil();
        } catch (Exception e) {
            throw new ProofInputException(e);
        } finally {
            if (cinp != null) {
                try {
                    cinp.close();
                } catch (IOException ioe) {
                    throw new ProofInputException(ioe);
                }
            }
        }
    }

    public Namespace<@NonNull QuantifiableVariable> variables() {
        return variables;
    }

    public Namespace<@NonNull SchemaVariable> schemaVariables() {
        return schemaVariables;
    }
}
