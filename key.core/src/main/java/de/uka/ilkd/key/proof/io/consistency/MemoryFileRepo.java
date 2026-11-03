/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io.consistency;

import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.file.Path;

import de.uka.ilkd.key.proof.io.RuleSource;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class uses the memory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
@NullMarked
public class MemoryFileRepo extends AbstractFileRepo {

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable InputStream getInputStream(Path path) {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; the difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable InputStream getInputStream(RuleSource ruleSource) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public @Nullable InputStream getInputStream(URL url) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public @Nullable OutputStream createOutputStream(Path path) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public @Nullable InputStream getInputStreamInternal(Path p) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public @Nullable Path getSaveName(Path path) {
        // TODO Auto-generated method stub
        return null;
    }
}
