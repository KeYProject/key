/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import org.key_project.rusty.proof.Proof;

public class ProofSaver extends OutputStreamProofSaver {
    /**
     * Save this proof to a file
     *
     * @param file file to save proof in
     * @param proof the {@link Proof} to be saved
     * @throws IOException on any I/O error
     */
    public static void saveToFile(File file, Proof proof) throws IOException {
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
    public static void saveProofObligationToFile(File file, Proof proof) throws IOException {
        ProofSaver saver = new ProofSaver(proof, file, false);
        saver.save();
    }


    private final File file;

    public ProofSaver(Proof proof, String fileName, String internalVersion) {
        this(proof, new File(fileName), internalVersion);
    }

    public ProofSaver(Proof proof, File file) {
        this(proof, file, "2.13.2 (Rusty)");
    }

    public ProofSaver(Proof proof, File file, String internalVersion) {
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
    public ProofSaver(Proof proof, File file, boolean saveProofSteps) {
        this(proof, file, "2.12.3 (Rusty)", saveProofSteps);
    }

    /**
     * Create a new proof saver.
     *
     * @param proof proof to save
     * @param file file to save proof into
     * @param internalVersion version of KeY to add to the proof log
     * @param saveProofSteps whether to save proof steps (false -> only proof obligation)
     */
    public ProofSaver(Proof proof, File file, String internalVersion, boolean saveProofSteps) {
        super(proof, internalVersion, saveProofSteps);
        this.file = file;
    }

    /**
     * Save the proof to file referenced by {@code file}.
     *
     * The format in which the proof is stored depends on the class. Thr base class creates a plain
     * output file. Subclasses may choose to use other formats.
     *
     * @param file the file to write to
     * @throws IOException if I/O fails
     */
    protected void save(File file) throws IOException {
        save(new FileOutputStream(file));
    }

    public String save() {
        String errorMsg = null;
        try {
            save(file);
        } catch (IOException ioe) {
            errorMsg = "Could not save \n" + filename() + ".\n";
            errorMsg += ioe.toString();
            // LOGGER.warn("Failed to save ", ioe);
        } catch (NullPointerException npe) {
            errorMsg = "Could not save \n" + filename() + "\n";
            errorMsg += "No proof present?";
            // LOGGER.warn("No proof present? ", npe);
        } catch (RuntimeException e) {
            errorMsg = e.toString();
            // LOGGER.warn("Failed to save ", e);
        }
        // fireProofSaved(new ProofSaverEvent(this, filename(), errorMsg));
        return errorMsg;
    }

    private String filename() {
        return file.getAbsolutePath();
    }
}
