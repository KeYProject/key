package de.uka.ilkd.key.gui;

import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.19)
 */
public class KeyboardTacletTest {

    @Test
    public void prefixTest() {
        assertEquals(3, KeyboardTacletModel.getPrefixLength("andLeft", "andRight"));
        assertEquals(3, KeyboardTacletModel.getPrefixLength("cut", "cut_direct"));
        assertEquals(0, KeyboardTacletModel.getPrefixLength("andLeft", "impRight"));


        List<String> keywords = Arrays.asList("cut", "cut_direct", "andLeft", "andRight", "impRight");

        assertEquals(3, KeyboardTacletModel.getClashFreePrefix("impLeft", keywords));

        Map<String, String> table = KeyboardTacletModel.buildPrefixTable(keywords);
        List<String> prefixes = table.keySet().stream().sorted().collect(Collectors.toList());
        assertEquals("[andL, andR, cut, cut_, i]", prefixes.toString());
    }
}