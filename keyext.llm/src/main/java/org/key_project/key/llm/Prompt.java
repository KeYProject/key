/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

/**
 * A user-defined reusable prompt: a message template with a name and a description. The template
 * may use the same markup as the input box ({@code $tokens}, {@code @files}, {@code /directives}).
 *
 * @param name unique id (also the file name)
 * @param description shown in menus/autocompletion
 * @param template the message template
 */
public record Prompt(String name, String description, String template) {

    public Prompt {
        name = name == null ? "" : name;
        description = description == null ? "" : description;
        template = template == null ? "" : template;
    }
}
