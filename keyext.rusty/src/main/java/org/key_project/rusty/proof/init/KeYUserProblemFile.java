/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;

import org.key_project.logic.Name;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.parser.KeYAst;
import org.key_project.rusty.parser.ProofReplayer;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.io.IProofFileParser;
import org.key_project.rusty.proof.io.KeYFile;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.rusty.settings.Configuration;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.rusty.speclang.SLEnvInput;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;

public class KeYUserProblemFile extends KeYFile implements ProofOblInput {
    private Sequent problem = null;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates a new representation of a KeYUserFile with the given name, a rule source representing
     * the physical source of the input, and a graphical representation to call back in order to
     * report the progress while reading.
     *
     * @param name the name of the file
     * @param file the file to read from
     * @param profile the KeY profile under which to load
     */
    public KeYUserProblemFile(String name, File file, Profile profile) {
        this(name, file, profile, false);
    }

    /**
     * Instantiates a new user problem file.
     *
     * @param name the name of the file
     * @param file the file to read from
     * @param profile the KeY profile under which to load
     * @param compressed {@code true} iff the file is compressed
     */
    public KeYUserProblemFile(String name, File file, Profile profile,
            boolean compressed) {
        super(name, file, profile, compressed);
    }

    /**
     * Instantiates a new user problem file.
     *
     * @param name the name of the file
     * @param file the file tp read from
     * @param fileRepo the fileRepo which will store the file
     * @param profile the KeY profile under which to load
     * @param compressed {@code true} iff the file is compressed
     */
    public KeYUserProblemFile(String name, File file, FileRepo fileRepo, Profile profile,
            boolean compressed) {
        super(name, file, fileRepo, profile, compressed);
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public ImmutableSet<String> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        ProofSettings settings = getPreferences();
        initConfig.setSettings(settings);

        ImmutableSet<String> warnings = DefaultImmutableSet.nil();

        // read key file itself (except contracts)
        warnings = warnings.union(super.readExtendedSignature());

        // read in-code specifications
        SLEnvInput slEnvInput = new SLEnvInput(readRustPath(),
            getProfile(), null);
        slEnvInput.setInitConfig(initConfig);
        ImmutableSet<String> read = slEnvInput.read();
        if (read != null)
            warnings = warnings.union(read);

        // read taclets
        // TODO: warnings = warnings.add(getPositionedStrings(readRules()));

        return warnings;
    }

    @Override
    public void readProblem() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("KeYUserProblemFile: InitConfig not set.");
        }

        try {
            problem = getProblemFinder().getProblem();
            if (problem == null) {
                boolean chooseDLContract = chooseContract() != null;
                boolean proofObligation = getProofObligation() != null;
                if (!chooseDLContract && !proofObligation) {
                    throw new ProofInputException(
                        "No \\problem or \\chooseContract or \\proofObligation in the input file!");
                }
            }
        } catch (Exception e) {
            throw new ProofInputException(e);
        }
    }

    @Override
    public Configuration getProofObligation() {
        return getProblemFinder().getProofObligation();
    }

    @Override
    public ProofAggregate getPO() {
        assert problem != null;
        Name name = name();
        ProofSettings settings = getPreferences();
        initConfig.setSettings(settings);
        return ProofAggregate.createProofAggregate(
            new Proof(name, problem, initConfig),
            name.toString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getProfile() {
        // TODO
        return RustProfile.getDefaultInstance();
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }

    /**
     * Reads a saved proof of a .key file.
     */
    public void readProof(IProofFileParser prl) throws IOException {
        KeYAst.File ctx = getParseContext();
        Token token = ctx.findProof();
        if (token != null) {
            CharStream stream = file.getCharStream();
            // also pass the file to be able to produce exceptions with locations
            try {
                ProofReplayer.run(token, stream, prl, file.url().toURI());
            } catch (URISyntaxException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
