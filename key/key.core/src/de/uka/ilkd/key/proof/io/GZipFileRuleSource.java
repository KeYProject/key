package de.uka.ilkd.key.proof.io;

import java.io.*;
import java.util.zip.GZIPInputStream;

/**
 * Created by tbormer on 12.02.16.
 */
public class GZipFileRuleSource extends FileRuleSource {

    GZipFileRuleSource(File ruleFile) {
        super(ruleFile);
    }

    @Override
    public InputStream getNewStream() {
        try {
            return new GZIPInputStream(new FileInputStream(ruleFile));
        } catch (final FileNotFoundException exception) {
            throw new RuntimeException("Error while reading rules.", exception);
        } catch (IOException e) {
            e.printStackTrace();
            throw new RuntimeException("Error while reading rules.", e);
        }
    }
}
