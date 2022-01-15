package de.uka.ilkd.key.rule.tacletbuilder;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public class BranchingNamingFunctionsTest {
    @Test public void parseNamingFunctionsNames() {
        assertArrayEquals(new String[]{"\\test"}, BranchingNamingFunctions.parse("\\test"));
        assertArrayEquals(new String[]{"\\test"}, BranchingNamingFunctions.parse("\\test()"));
        assertArrayEquals(new String[]{"\\test", "a"}, BranchingNamingFunctions.parse("\\test(a)"));
        assertArrayEquals(new String[]{"\\test", "a","b"}, BranchingNamingFunctions.parse("\\test(a,b)"));
        assertArrayEquals(new String[]{"\\test", "a","b"}, BranchingNamingFunctions.parse("\\test(  a  ,  b  )"));
        assertArrayEquals(new String[]{"\\nameLabelOf", "#b"}, BranchingNamingFunctions.parse("\\nameLabelOf(#b)"));
        }
}