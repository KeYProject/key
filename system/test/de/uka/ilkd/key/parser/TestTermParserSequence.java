package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.AbstractProfile;

/**
 * Testing pretty-printing and parsing of seqGet terms in this class.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserSequence extends AbstractTestTermParser {

    public TestTermParserSequence() {
        super(TestTermParserSequence.class.getSimpleName());
    }

    @Override
    protected Services getServices() {
        return new Services(AbstractProfile.getDefaultProfile());
    }

    @Override
    public void setUp() {
    }

    public void test() {
    }

}
