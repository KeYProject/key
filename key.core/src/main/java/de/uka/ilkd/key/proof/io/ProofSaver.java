/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Saves a proof and provides useful methods for pretty printing terms or programs.
 */
public class ProofSaver extends OutputStreamProofSaver {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSaver.class);

    /**
     * First-line marker denoting a closed proof, as written with
     * {@link ProofSaver#marker(boolean, int)}.
     */
    public static final String KEY_PROOF_STATUS_CLOSED = "KEY_PROOF_STATUS closed 0";

    /**
     * Prefix for the marker denoting an open (unclosed) proof. The number of open goals is appended
     * after this prefix.
     */
    public static final String KEY_PROOF_STATUS_OPEN_PREFIX = "KEY_PROOF_STATUS open ";

    /**
     * Prefix shared by all {@code KEY_PROOF_STATUS *} markers. A first line starting with this
     * prefix is treated as a status marker.
     */
    public static final String KEY_PROOF_STATUS_PREFIX = "KEY_PROOF_STATUS";

    /**
     * Build the status marker line for a proof.
     *
     * @param closed whether the proof is closed
     * @param openGoals the number of open goals
     * @return the marker string, e.g. {@code "KEY_PROOF_STATUS closed 0"} or
     *         {@code "KEY_PROOF_STATUS open 3"}
     */
    public static String marker(boolean closed, int openGoals) {
        return closed ? KEY_PROOF_STATUS_CLOSED : KEY_PROOF_STATUS_OPEN_PREFIX + openGoals;
    }

    /**
     * Save this proof to a file
     *
     * @param file file to save proof in
     * @param proof the {@link Proof} to be saved
     * @throws IOException on any I/O error
     */
    public static void saveToFile(File file, Proof proof) throws IOException {
        saveToFile(file.toPath(), proof);
    }

    public static void saveToFile(Path file, Proof proof) {
        ProofSaver saver = new ProofSaver(proof, file);
        saver.save();
    }

    /**
     * Save this proof to a file, prepending the given header line before the proof content. A
     * {@code null} header writes no header line (backwards compatible).
     *
     * @param file file to save proof in
     * @param proof the {@link Proof} to be saved
     * @param headerLine optional first line to write before the proof content, or {@code null}
     * @return an error message on failure, or {@code null} on success
     */
    public static String saveToFile(Path file, Proof proof, @Nullable String headerLine) {
        ProofSaver saver = new ProofSaver(proof, file);
        saver.headerLine = headerLine;
        return saver.save();
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
            save(file.getParent(), out);
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
