/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.io.File;
import java.util.List;

import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.init.Profile;

/**
 * This single threaded problem loader is used by the Eclipse integration of KeY.
 *
 * @author Martin Hentschel
 */
public class SingleThreadProblemLoader extends AbstractProblemLoader {
    /**
     * Constructor.
     *
     * @param file The file or folder to load.
     * @param includes Optional includes to consider.
     * @param profileOfNewProofs The {@link Profile} to use for new {@link Proof}s.
     * @param control The {@link ProblemLoaderControl} to use.
     */
    public SingleThreadProblemLoader(File file, List<File> includes, Profile profileOfNewProofs,
            ProblemLoaderControl control) {
        super(file, includes, profileOfNewProofs,
            control);
    }
}
