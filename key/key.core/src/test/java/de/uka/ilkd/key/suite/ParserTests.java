package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        de.uka.ilkd.key.parser.TestDeclParser.class,
//        de.uka.ilkd.key.parser.TestParallelParsing.class,
        de.uka.ilkd.key.parser.TestTermParser.class,
        de.uka.ilkd.key.parser.TestTermParserHeap.class,
        de.uka.ilkd.key.parser.TestTermParserSorts.class,
        de.uka.ilkd.key.parser.TestJMLParserAssociativity.class,
        de.uka.ilkd.key.parser.TestTacletParser.class,
})
public class ParserTests {
}