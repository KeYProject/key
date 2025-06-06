/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.event.ProofSaverEvent;
import de.uka.ilkd.key.proof.io.event.ProofSaverListener;
import de.uka.ilkd.key.util.KeYConstants;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Saves a proof and provides useful methods for pretty printing terms or programs.
 */
public class ProofSaver extends OutputStreamProofSaver {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSaver.class);

    /**
     * Save this proof to a file
     *
     * @param file file to save proof in
     * @param proof the {@link Proof} to be saved
     * @throws IOException on any I/O error
     */
    public static void saveToFile(File file, Proof proof) throws IOException {
        saveProofObligationToFile(file.toPath(), proof);
    }

    public static void saveToFile(Path file, Proof proof) throws IOException {
        ProofSaver saver = new ProofSaver(proof, file);
        saver.save();
    }

    /**
     * Save this proof to a file whilst omitting all proof steps.
     * In effect, this only saves the proof obligation.
     *
     * @param file file to save proof in
     * @param proof the {@link Proof} to be saved
     * @throws IOException on any I/O error
     */
    public static void saveProofObligationToFile(Path file, Proof proof) throws IOException {
        ProofSaver saver = new ProofSaver(proof, file, false);
        saver.save();
    }


    private final Path file;

    /**
     * <p>
     * Contains all listener.
     * </p>
     * <p>
     * They are used for instance by the Eclipse integration to refresh the workspace when a proof
     * file was saved.
     * </p>
     * .
     */
    private static final List<ProofSaverListener> listeners = new LinkedList<>();

    public ProofSaver(Proof proof, String fileName, String internalVersion) {
        this(proof, Paths.get(fileName), internalVersion);
    }

    public ProofSaver(Proof proof, Path file) {
        this(proof, file, KeYConstants.INTERNAL_VERSION);
    }

    public ProofSaver(Proof proof, Path file, String internalVersion) {
        super(proof, internalVersion);
        this.file = file;
    }

    /**
     * Create a new proof saver.
     *
     * @param proof proof to save
     * @param file file to save proof into
     * @param saveProofSteps whether to save proof steps (false -> only proof obligation)
     */
    public ProofSaver(Proof proof, Path file, boolean saveProofSteps) {
        this(proof, file, KeYConstants.INTERNAL_VERSION, saveProofSteps);
    }

    /**
     * Create a new proof saver.
     *
     * @param proof proof to save
     * @param file file to save proof into
     * @param internalVersion version of KeY to add to the proof log
     * @param saveProofSteps whether to save proof steps (false -> only proof obligation)
     */
    public ProofSaver(Proof proof, Path file, String internalVersion, boolean saveProofSteps) {
        super(proof, internalVersion, saveProofSteps);
        this.file = file;
    }

    /**
     * Save the proof to file referenced by {@code file}.
     * <p>
     * The format in which the proof is stored depends on the class. Thr base class creates a plain
     * output file. Subclasses may choose to use other formats.
     *
     * @param file the file to write to
     * @throws IOException if I/O fails
     */
    protected void save(Path file) throws IOException {
        try (var out = Files.newOutputStream(file)) {
            save(out);
        }
    }

    public String save() {
        String errorMsg = null;
        try {
            save(file);
        } catch (IOException ioe) {
            errorMsg = "Could not save \n" + filename() + ".\n";
            errorMsg += ioe.toString();
            LOGGER.warn("Failed to save ", ioe);
        } catch (NullPointerException npe) {
            errorMsg = "Could not save \n" + filename() + "\n";
            errorMsg += "No proof present?";
            LOGGER.warn("No proof present? ", npe);
        } catch (RuntimeException e) {
            errorMsg = e.toString();
            LOGGER.warn("Failed to save ", e);
        }
        fireProofSaved(new ProofSaverEvent(this, filename().toString(), errorMsg));
        return errorMsg;
    }

    @Override
    protected Path getBasePath() throws IOException {
        return computeBasePath(file);
    }

    /**
     * Computes the base path of the given proof {@link File}.
     * <p>
     * This method is used by {@link #getBasePath()} and by the Eclipse integration.
     *
     * @param proofFile The proof {@link File}.
     * @return The computed base path of the given proof {@link File}.
     */
    public static Path computeBasePath(Path proofFile) {
        return proofFile.toAbsolutePath().getParent().toAbsolutePath();
    }

    /**
     * Adds the {@link ProofSaverListener}.
     *
     * @param l The {@link ProofSaverListener} to add.
     */
    public static void addProofSaverListener(ProofSaverListener l) {
        if (l != null) {
            listeners.add(l);
        }
    }

    /**
     * Removes the {@link ProofSaverListener}.
     *
     * @param l The {@link ProofSaverListener} to remove.
     */
    public static void removeProofSaverListener(ProofSaverListener l) {
        if (l != null) {
            listeners.remove(l);
        }
    }

    /**
     * Informs all listener about the event {@link ProofSaverListener#proofSaved(ProofSaverEvent)}.
     *
     * @param e The event.
     */
    protected static void fireProofSaved(ProofSaverEvent e) {
        ProofSaverListener[] toInform = listeners.toArray(new ProofSaverListener[0]);
        for (ProofSaverListener l : toInform) {
            l.proofSaved(e);
        }
    }

    private Path filename() {
        return file.toAbsolutePath();
    }

}
