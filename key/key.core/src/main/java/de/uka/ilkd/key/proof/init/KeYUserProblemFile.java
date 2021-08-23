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

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.ChoiceInformation;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.ProblemInformation;
import de.uka.ilkd.key.nparser.ProofReplayer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.io.IProofFileParser;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.key.util.Triple;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import javax.annotation.Nonnull;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import java.io.File;
import java.io.IOException;


/**
 * Represents an input from a .key user problem file producing an environment
 * as well as a proof obligation.
 */
public final class KeYUserProblemFile extends KeYFile implements ProofOblInput {
    private Term problemTerm = null;

    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 

    /**
     * Creates a new representation of a KeYUserFile with the given name,
     * a rule source representing the physical source of the input, and
     * a graphical representation to call back in order to report the progress
     * while reading.
     * @param name    the name of the file
     * @param file    the file to read from
     * @param monitor the possibly <tt>null</tt> monitor for progress
     * @param profile the KeY profile under which to load
     */
    public KeYUserProblemFile(String name,
                              File file,
                              ProgressMonitor monitor,
                              Profile profile) {
        this(name, file, monitor, profile, false);
    }

    /**
     * Instantiates a new user problem file.
     *
     * @param name       the name of the file
     * @param file       the file to read from
     * @param monitor    the possibly <tt>null</tt> monitor for progress
     * @param profile    the KeY profile under which to load
     * @param compressed {@code true} iff the file is compressed
     */
    public KeYUserProblemFile(String name,
                              File file,
                              ProgressMonitor monitor,
                              Profile profile,
                              boolean compressed) {
        super(name, file, monitor, profile, compressed);
    }

    /**
     * Instantiates a new user problem file.
     *
     * @param name       the name of the file
     * @param file       the file tp read from
     * @param fileRepo   the fileRepo which will store the file
     * @param monitor    the possibly <tt>null</tt> monitor for progress
     * @param profile    the KeY profile under which to load
     * @param compressed {@code true} iff the file is compressed
     */
    public KeYUserProblemFile(String name,
                              File file,
                              FileRepo fileRepo,
                              ProgressMonitor monitor,
                              Profile profile,
                              boolean compressed) {
        super(name, file, fileRepo, monitor, profile, compressed);
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        ProofSettings settings = getPreferences();
        initConfig.setSettings(settings);

        ChoiceInformation ci = getParseContext().getChoices();
        settings.getChoiceSettings().updateWith(ci.getActivatedChoices());
        initConfig.setActivatedChoices(
                settings.getChoiceSettings().getDefaultChoicesAsSet());

        //read in-code specifications
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        SLEnvInput slEnvInput = new SLEnvInput(readJavaPath(),
                readClassPath(),
                readBootClassPath(), getProfile(), null);
        slEnvInput.setInitConfig(initConfig);
        warnings = warnings.union(slEnvInput.read());

        //read key file itself
        ImmutableSet<PositionedString> parent = super.read();
        warnings = warnings.union(parent);
        return warnings;
    }

    @Override
    public void readProblem() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("KeYUserProblemFile: InitConfig not set.");
        }

        readSorts();
        readFuncAndPred();
        readRules();


        try {
            problemTerm = getProblemFinder().getProblemTerm();
            if (problemTerm == null) {
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
    public String chooseContract() {
        return getProblemFinder().getChooseContract();
    }

    @Override
    public String getProofObligation() {
        return getProblemFinder().getProofObligation();
    }

    @Override
    public ProofAggregate getPO() throws ProofInputException {
        assert problemTerm != null;
        String name = name();
        ProofSettings settings = getPreferences();
        initConfig.setSettings(settings);
        return ProofAggregate.createProofAggregate(
                new Proof(name,
                        problemTerm,
                        getParseContext().getProblemHeader()+"\n",
                        initConfig),
                name);
    }


    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }


    public boolean hasProofScript() {
        return getParseContext().findProofScript() != null;
    }

    public Triple<String, Integer, Integer> readProofScript() throws ProofInputException {
        return getParseContext().findProofScript();
    }

    /**
     * Reads a saved proof of a .key file.
     */
    public void readProof(IProofFileParser prl) throws IOException {
        KeyAst.File ctx = getParseContext();
        Token token = ctx.findProof();
        if (token != null) {
            CharStream stream = file.getCharStream();
            ProofReplayer.run(token, stream, prl);
        }
    }


    @Override
    public boolean equals(Object o) {
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        final KeYUserProblemFile kf = (KeYUserProblemFile) o;
        return kf.file.file().getAbsolutePath()
                .equals(file.file().getAbsolutePath());
    }


    @Override
    public int hashCode() {
        return file.file().getAbsolutePath().hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Profile getProfile() {
        try {
            Profile profile = readProfileFromFile();
            if (profile != null) {
                return profile;
            } else {
                return getDefaultProfile();
            }
        } catch (Exception e) {
            return getDefaultProfile();
        }
    }

    /**
     * Tries to read the {@link Profile} from the file to load.
     *
     * @return The {@link Profile} defined by the file to load or {@code null} if no {@link Profile} is defined by the file.
     * @throws Exception Occurred Exception.
     */
    protected Profile readProfileFromFile() throws Exception {
        @Nonnull ProblemInformation pi = getProblemInformation();
        String profileName = pi.getProfile();
        if (profileName != null && !profileName.isEmpty()) {
            return ProofInitServiceUtil.getDefaultProfile(profileName);
        } else {
            return null;
        }
    }

    /**
     * Returns the default {@link Profile} which was defined by a constructor.
     *
     * @return The default {@link Profile}.
     */
    protected Profile getDefaultProfile() {
        return super.getProfile();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return null;
    }
}
