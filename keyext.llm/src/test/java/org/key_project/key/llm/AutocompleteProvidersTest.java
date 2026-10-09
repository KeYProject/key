/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests that the {@code /} completion provider filters by the word typed behind the trigger
 * character (the leading {@code /} is not part of the prefix the input component passes in).
 */
class AutocompleteProvidersTest {

    private static AutocompleteInput.CompletionProvider commands() {
        return AutocompleteProviders.commands(() -> {
        }, () -> {
        });
    }

    @Test
    void emptyPrefixListsAllCommands() {
        var all = commands().apply("");
        assertTrue(all.stream().anyMatch(s -> "/skills".equals(s.label())));
        assertTrue(all.stream().anyMatch(s -> "/prompts".equals(s.label())));
        assertTrue(all.stream().anyMatch(s -> s.label().contains("new skill")));
    }

    @Test
    void typingFiltersWithoutMatchingAgainstTheSlash() {
        var filtered = commands().apply("ski");
        assertFalse(filtered.isEmpty(), "typing after '/' must keep the matching commands");
        assertTrue(filtered.stream().anyMatch(s -> "/skills".equals(s.label())),
            filtered::toString);
        assertTrue(filtered.stream().noneMatch(s -> "/prompts".equals(s.label())));
    }

    @Test
    void slashDirectiveMatchesTheNameBehindTheSlash() {
        var filtered = commands().apply("skill:opt");
        // with no user-defined skills the list is empty; in any case "/skills" must not match here
        assertTrue(filtered.stream().noneMatch(s -> "/skills".equals(s.label())));
        assertTrue(
            filtered.stream().allMatch(s -> s.label().startsWith("/skill:")) || filtered.isEmpty(),
            filtered::toString);
    }
}
