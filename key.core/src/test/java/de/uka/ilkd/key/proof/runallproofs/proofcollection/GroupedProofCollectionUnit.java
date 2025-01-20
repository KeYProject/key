/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

/**
 * A {@link ProofCollectionUnit} that is created from several {@link TestFile}s that are grouped
 * together.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class GroupedProofCollectionUnit extends ProofCollectionUnit {

    private static final long serialVersionUID = 1L;
    private final String groupName;
    private final List<TestFile> testFiles;
    private final ProofCollectionSettings settings;

    public GroupedProofCollectionUnit(String groupName, ProofCollectionSettings settings) {
        this.groupName = groupName;
        this.settings = new ProofCollectionSettings(settings);
        this.testFiles = new ArrayList<>();
    }

    @Override
    public RunAllProofsTestUnit createRunAllProofsTestUnit(String testName) {
        return new RunAllProofsTestUnit(testName, settings, testFiles, false);
    }

    @Override
    String getName() {
        return groupName;
    }

    public TestFile provable(String path) throws IOException {
        RunAllProofsDirectories.init();
        var tf = new TestFile(TestProperty.PROVABLE, path, settings);
        testFiles.add(tf);
        return tf;
    }

    public TestFile notprovable(String path) throws IOException {
        RunAllProofsDirectories.init();
        var tf = new TestFile(TestProperty.NOTPROVABLE, path, settings);
        testFiles.add(tf);
        return tf;
    }

    public TestFile loadable(String path) throws IOException {
        RunAllProofsDirectories.init();
        var tf = new TestFile(TestProperty.LOADABLE, path, settings);
        testFiles.add(tf);
        return tf;
    }

    public TestFile notloadable(String path) throws IOException {
        RunAllProofsDirectories.init();
        var tf = new TestFile(TestProperty.NOTLOADABLE, path, settings);
        testFiles.add(tf);
        return tf;
    }

    public void setLocalSettings(String s) {
        settings.setLocalKeYSettings(s);
    }

    public void setDirectory(String s) {
        settings.setDirectory(s);
    }
}
