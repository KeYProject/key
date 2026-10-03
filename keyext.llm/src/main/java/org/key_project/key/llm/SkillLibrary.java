/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import com.google.gson.GsonBuilder;

/**
 * The file-backed library of user-defined skills. An active skill is selected on the
 * {@link LlmSession}; its instructions are appended to the system prompt and its
 * {@code allowedTools} whitelist narrows the advertised tool set.
 *
 * @author Alexander Weigl
 */
public final class SkillLibrary extends FileBackedLibrary<Skill> {
    public static final SkillLibrary INSTANCE = new SkillLibrary();

    private SkillLibrary() {
    }

    @Override
    protected String subDirectory() {
        return "skills";
    }

    @Override
    protected Skill fromJson(String json) {
        try {
            return new GsonBuilder().create().fromJson(json, Skill.class);
        } catch (Exception e) {
            return null;
        }
    }

    @Override
    protected String toJson(Skill element) {
        return new GsonBuilder().setPrettyPrinting().create().toJson(element);
    }

    @Override
    protected String nameOf(Skill element) {
        return element.name();
    }

    @Override
    protected String validate(Skill element) {
        if (!validName(element.name())) {
            return "Name may only contain letters, digits, '_' and '-'.";
        }
        return null;
    }
}
