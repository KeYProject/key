package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({de.uka.ilkd.key.speclang.jml.translation.TestJMLTranslator.class,
        de.uka.ilkd.key.speclang.jml.pretranslation.TestJMLPreTranslator.class
})
public class SpeclangTests {
}
