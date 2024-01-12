/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * Used for TESTS ONLY as we allow there to declare program variables global in rule files.
 */
public class KeYFileForTests extends KeYFile {

    private Namespace<QuantifiableVariable> variables;
    private Namespace<SchemaVariable> schemaVariables;

    /**
     * creates a new representation for a given file by indicating a name and a file representing
     * the physical source of the .key file.
     */
    public KeYFileForTests(String name, File file, Profile profile) {
        super(name, file, null, profile);
    }

    /**
     * reads the whole .key file and modifies the initial configuration assigned to this object
     * according to the given modification strategy. Throws an exception if no initial configuration
     * has been set yet.
     */
    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("KeYFile: InitConfig not set.");
        }
        CountingBufferedReader cinp = null;
        try {
            cinp = new CountingBufferedReader(getNewStream(), monitor, getNumberOfChars() / 100);
            final ParserConfig pc =
                new ParserConfig(initConfig.getServices(), initConfig.namespaces());
            KeyIO io = new KeyIO(initConfig.getServices());
            KeyIO.Loader l = io.load(file.getCharStream());
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

    // public Includes readIncludes() throws ProofInputException {
    // Includes result = super.readIncludes();
    //
    // //add test LDTs
    // if(result.getLDTIncludes().isEmpty()) {
    // result.put("ldtsForTests",
    // RuleSourceFactory.initRuleFile("ldt.key"));
    // }
    //
    // return result;
    // }

    public Namespace<QuantifiableVariable> variables() {
        return variables;
    }

    public Namespace<SchemaVariable> schemaVariables() {
        return schemaVariables;
    }
}
