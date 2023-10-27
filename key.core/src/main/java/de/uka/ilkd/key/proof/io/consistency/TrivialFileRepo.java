/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.io.RuleSource;

/**
 * This FileRepo does not cache any files but writes to / reads from the original files on disk. It
 * can be used for recreating the old behavior of KeY without a FileRepo.
 *
 * @author Wolfram Pfeifer
 */
public class TrivialFileRepo implements FileRepo {
    @Override
    public InputStream getInputStream(Path path) throws IOException {

        // wrap path into URL for uniform treatment
        return getInputStream(path.toUri().toURL());
    }

    @Override
    public InputStream getInputStream(RuleSource ruleSource) {
        return ruleSource.getNewStream();
    }

    @Override
    public InputStream getInputStream(URL url) throws IOException {
        return url.openStream();
    }

    @Override
    public OutputStream createOutputStream(Path path) throws FileNotFoundException {
        return new FileOutputStream(path.toFile());
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        // since there are no copies, nothing has to be cleaned
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        // since there are no copies, nothing has to be cleaned
    }

    @Override
    public void registerProof(Proof proof) {
        // nothing to do here
    }

    @Override
    public void setBootClassPath(File path) throws IllegalStateException {
        // nothing to do here
    }

    @Override
    public void setClassPath(List<File> classPath) throws IllegalStateException {
        // nothing to do here
    }

    @Override
    public void setJavaPath(String javaPath) throws IllegalStateException {
        // nothing to do here
    }

    @Override
    public void setBaseDir(Path path) {
        // nothing to do here
    }
}
