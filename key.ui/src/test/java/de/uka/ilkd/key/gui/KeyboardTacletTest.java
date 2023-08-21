/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

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


        List<String> keywords =
            Arrays.asList("cut", "cut_direct", "andLeft", "andRight", "impRight");

        assertEquals(3, KeyboardTacletModel.getClashFreePrefix("impLeft", keywords));

        Map<String, String> table = KeyboardTacletModel.buildPrefixTable(keywords);
        List<String> prefixes = table.keySet().stream().sorted().collect(Collectors.toList());
        assertEquals("[andL, andR, cut, cut_, i]", prefixes.toString());
    }
}
