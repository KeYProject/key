package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.util.Date;
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

    public GroupedProofCollectionUnit(String groupName, ProofCollectionSettings settings,
            List<TestFile> files) {
        this.groupName = groupName;
        this.settings = settings;
        this.testFiles = files;
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
        var tf = new TestFile(TestProperty.PROVABLE, path, settings,
            new RunAllProofsDirectories(new Date()));
        testFiles.add(tf);
        return tf;
    }

    public TestFile notprovable(String path) throws IOException {
        var tf = new TestFile(TestProperty.NOTPROVABLE, path, settings,
            new RunAllProofsDirectories(new Date()));
        testFiles.add(tf);
        return tf;
    }

    public TestFile loadable(String path) throws IOException {
        var tf = new TestFile(TestProperty.LOADABLE, path, settings,
            new RunAllProofsDirectories(new Date()));
        testFiles.add(tf);
        return tf;
    }

    public TestFile notloadable(String path) throws IOException {
        var tf = new TestFile(TestProperty.NOTLOADABLE, path, settings,
            new RunAllProofsDirectories(new Date()));
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
